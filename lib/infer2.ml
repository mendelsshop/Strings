open Expr.Types
open Expr
open Monad
open Monad.ResultReaderOps
open Utils

let generalize =
  List.fold ~init:([], MetaVariables.empty)
    ~f:(fun (variables, metavariables) ((name : string), (ty : ty)) ->
      let* metavariables' = generalize ty in
      return
        ( (name, Types.TPoly (metavariables', ty)) :: variables,
          MetaVariables.union metavariables metavariables' ))

let rec solver = function
  | [] -> return Subst.empty
  | (t1, t2) :: cs' ->
      let* subs = unify t1 t2 in
      let open SubstitableA (SubstitableConstraint) in
      let* subs' = apply subs cs' |> solver in
      compose subs subs' |> return

let rec infer_pattern = function
  | PVar x ->
      let* ty = new_meta in
      return ([ (x, ty) ], ty, PTVar (x, ty))
  | PWildcard ->
      let* ty = new_meta in
      return ([], ty, PTWildcard ty)
  | PBoolean b -> return ([], TBool, PTBoolean (b, TBool))
  | PNumber b -> return ([], TInt, PTNumber (b, TInt))
  | PTuple (t1, t2) ->
      let* env1, e1_ty, t1' = infer_pattern t1 in
      let* env2, e2_ty, t2' = infer_pattern t2 in
      let ty = Types.TTuple (e1_ty, e2_ty) in
      return (env1 @ env2, ty, PTTuple (t1', t2', ty))

let infer_expr expr =
  let rec infer_inner expr =
    match expr with
    | Var x ->
        x |> get
        |> bind ~f:(fun ty ->
               let* ty' = instantiate ty in
               return ([], ty', TVar (x, ty')))
    | Boolean b -> return ([], TBool, TBoolean (b, TBool))
    | Number b -> return ([], TInt, TNumber (b, TInt))
    | If (cond, cons, alt) ->
        let* cs, cond_ty, cond' = infer_inner cond in
        let* cs', cons_ty, cons' = infer_inner cons in
        let* cs'', alt_ty, alt' = infer_inner alt in
        return
          ( ((cond_ty, TBool) :: (cond_ty, alt_ty) :: cs) @ cs' @ cs'',
            cons_ty,
            TIf (cond', cons', alt', cons_ty) )
    | Let (var, e1, e2) ->
        let* cs, e1_ty, e1' = infer_inner e1 in
        let* env, var_ty, var' = infer_pattern var in
        let cs' = (e1_ty, var_ty) :: cs in
        let* subs = cs' |> solver in
        (*subs |> Subst.to_list*)
        (*|> Stdlib.List.map (fun (meta, ty) -> meta ^ ": " ^ type_to_string ty)*)
        (*|> String.concat ", " |> print_endline;*)
        (*let e1_ty' = SubstitableType.apply subs e1_ty in*)
        let env' =
          Stdlib.List.map
            (fun (x, ty) -> (x, SubstitableType.apply subs ty))
            env
        in
        let* env'', metas = generalize env' in
        (*env''*)
        (*|> Stdlib.List.map (fun (meta, ty) -> meta ^ ": " ^ type_to_string ty)*)
        (*      |> String.concat "; " |> print_endline;*)
        let* cs'', e2_ty, e2' = in_env env'' (infer_inner e2) in
        (*TODO: maybe: be more specific about where we put our (P)TPolys so the annotations of type schemes are more targeted*)
        return
          ( cs' @ cs'',
            e2_ty,
            TLet (PTPoly (metas, var'), TPoly (metas, e1'), e2', e2_ty) )
    | Lambda (var, abs) ->
        let* env, var_ty, var' = infer_pattern var in
        let* cs, abs_ty, abs' = in_env env (infer_inner abs) in
        let ty = TArrow (var_ty, abs_ty) in
        return (cs, ty, TLambda (var', abs', ty))
    | Application (abs, arg) ->
        let* cs, abs_ty, abs' = infer_inner abs in
        let* cs', arg_ty, arg' = infer_inner arg in
        let* ret_ty = new_meta in
        return
          ( ((abs_ty, TArrow (arg_ty, ret_ty)) :: cs) @ cs',
            ret_ty,
            TApplication (abs', arg', ret_ty) )
    | Tuple (e1, e2) ->
        let* cs, e1_ty, e1' = infer_inner e1 in
        let* cs', e2_ty, e2' = infer_inner e2 in
        let ty = Types.TTuple (e1_ty, e2_ty) in
        return (cs @ cs', ty, TTuple (e1', e2', ty))
  in
  let* cs, _ty, expr' = infer_inner expr in
  let* subs = solver cs in
  let expr'' = SubstitableExpr.apply subs expr' in
  (expr'', type_of expr'') |> return

let rec infer :
    R.env -> ST.env -> program list -> (tprogram list * R.env, string) result =
 fun env letters -> function
  | [] -> Result.ok ([], env)
  | Bind (name, expr) :: tls ->
      let infer_generalize =
        let* (expr' : texpr), (expr_ty : ty) = infer_expr expr in
        let* _, metas = generalize [ (name, expr_ty) ] in
        (TPoly (metas, expr'), Expr.Types.TPoly (metas, expr_ty)) |> return
      in
      let expr', letters' = run infer_generalize env letters in

      Result.bind expr' (fun (expr'', expr_ty) ->
          infer ((name, expr_ty) :: env) letters' tls
          |> Result.map (fun (program, letters') ->
                 (Bind (name, expr'') :: program, letters')))
  | Expr expr :: tls ->
      let expr', letters' = run (infer_expr expr) env letters in
      Result.bind expr' (fun (expr'', _) ->
          infer env letters' tls
          |> Result.map (fun (program, letters') ->
                 (Expr expr'' :: program, letters')))

let infer env = Result.map fst << infer env letters
