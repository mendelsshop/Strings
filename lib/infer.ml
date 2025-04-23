open Expr.Types
open Expr
open Monad
open Monad.ResultReaderOps
open Utils

(*the list of variables here is the list of pattern variables we are generalizing*)
let generalize variables =
  let* variables, metas =
    List.fold ~init:([], MetaVariables.empty)
      ~f:(fun (variables, metavariables) ((name : string), (ty : ty)) ->
        let* metavariables' = generalize ty in
        return
          ( (name, Types.TPoly (metavariables', ty)) :: variables,
            MetaVariables.union metavariables metavariables' ))
      variables
  in
  return (variables, if MetaVariables.is_empty metas then None else Some metas)

let print_constraints cs =
  cs
  |> Stdlib.List.map (fun (ty, ty') ->
         type_to_string ty ^ "~=" ^ type_to_string ty')
  |> String.concat "\n" |> print_endline

let rec solver = function
  | [] -> return Subst.empty
  | (t1, t2) :: cs ->
      let* subs = unify t1 t2 in
      let open SubstitableA (SubstitableConstraint) in
      let cs' = apply subs cs in
      let* subs' = cs' |> solver in
      let subs = Subst.map (SubstitableType.apply subs') subs in
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
  | PConstructor (name, pattern) ->
      let* other_variants = new_meta in
      let* env, ty, pattern' = infer_pattern pattern in
      let ty' = TVariant (TRowExtend (name, ty, other_variants)) in
      (env, ty', PTConstructor (name, pattern', ty')) |> return
  | PRecord row ->
      let* row_init = return ([], TRowEmpty, []) in
      let* env, pattern_ty, pattern =
        List.fold_right
          ~f:(fun (label, pattern) result ->
            let env, row_ty, row = result in
            let* env', pat_ty, pat' = infer_pattern pattern in
            return
              ( env @ env',
                TRowExtend (label, pat_ty, row_ty),
                (label, pat') :: row ))
          row ~init:row_init
      in
      let ty = Types.TRecord pattern_ty in
      return (env, ty, PTRecord (pattern, ty))

let infer_expr expr =
  let rec infer_inner expr =
    match expr with
    | Var x ->
        let* ty = get x in
        let* ty' = instantiate ty in
        return ([], ty', TVar (x, ty'))
    | Boolean b -> return ([], TBool, TBoolean (b, TBool))
    | Number b -> return ([], TInt, TNumber (b, TInt))
    | If (cond, cons, alt) ->
        let* cs, cond_ty, cond' = infer_inner cond in
        let* cs', cons_ty, cons' = infer_inner cons in
        let* cs'', alt_ty, alt' = infer_inner alt in
        return
          ( ((cond_ty, TBool) :: (cons_ty, alt_ty) :: cs) @ cs' @ cs'',
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
            Option.fold metas
              ~none:(TLet (var', e1', e2', e2_ty))
              ~some:(fun metas ->
                TLet (PTPoly (metas, var'), TPoly (metas, e1'), e2', e2_ty)) )
    | LetRec (var, e1, e2) ->
        let* env, var_ty, var' = infer_pattern var in
        let* cs, e1_ty, e1' = in_env env (infer_inner e1) in
        let cs' = (var_ty, e1_ty) :: cs in
        let* subs = cs' |> solver in
        let e1' = SubstitableExpr.apply subs e1' in
        let var' = SubstitablePattern.apply subs var' in
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
            Option.fold metas
              ~none:(TLetRec (var', e1', e2', e2_ty))
              ~some:(fun metas ->
                TLetRec (PTPoly (metas, var'), TPoly (metas, e1'), e2', e2_ty))
          )
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
    | Record row ->
        let* row_init = return ([], TRowEmpty, []) in

        let* cs, row_ty, row' =
          List.fold_right
            ~f:(fun (label, expr) result ->
              let cs, row_ty, row = result in
              let* cs', expr_ty, expr' = infer_inner expr in
              return
                ( cs @ cs',
                  TRowExtend (label, expr_ty, row_ty),
                  (label, expr') :: row ))
            row ~init:row_init
        in
        let ty = Types.TRecord row_ty in
        return (cs, ty, TRecord (row', ty))
    | Constructor (name, expr) ->
        let* other_variants = new_meta in
        let* cs, ty, expr' = infer_inner expr in
        let ty' = TVariant (TRowExtend (name, ty, other_variants)) in
        (cs, ty', TConstructor (name, expr', ty')) |> return
    | RecordAcces (record, label) ->
        let* ty = new_meta in
        let* rest_row = new_meta in
        let* cs, record_ty, record' = infer_inner record in
        return
          ( (Types.TRecord (TRowExtend (label, ty, rest_row)), record_ty) :: cs,
            ty,
            TRecordAcces (record', label, ty) )
    | Match (expr, cases) ->
        (*TODO: exhaustiveness*)
        let* cs, ty, expr' = infer_inner expr in
        let* ret = new_meta in
        let* cs', cases' =
          List.fold cases
            ~f:(fun (cs, cases) (pat, case) ->
              let* env, pat_ty, pat' = infer_pattern pat in
              let* cs', case_ty, case' = in_env env (infer_inner case) in
              let cs'' = cs @ cs' @ [ (ty, pat_ty); (ret, case_ty) ] in
              return (cs'', cases @ [ (pat', case') ]))
            ~init:(cs, [])
        in
        (cs', ret, TMatch (expr', cases', ret)) |> return
    | RecordExtend (record, row) ->
        let* cs, record_ty, record' = infer_inner record in
        let* record_check = new_meta in
        let* row_init = return (cs, record_check, []) in

        let* cs', row_ty, row' =
          List.fold_right
            ~f:(fun (label, expr) result ->
              let cs, row_ty, row = result in
              let* cs', expr_ty, expr' = infer_inner expr in
              return
                ( cs @ cs',
                  TRowExtend (label, expr_ty, row_ty),
                  (label, expr') :: row ))
            row ~init:row_init
        in
        ( (Types.TRecord record_check, record_ty) :: cs',
          Types.TRecord row_ty,
          TRecordExtend (record', row', row_ty) )
        |> return
  in
  let* cs, ty, expr' = infer_inner expr in
  let* subs = solver cs in
  let expr'' = SubstitableExpr.apply subs expr' in
  let ty' = SubstitableType.apply subs ty in
  (expr'', ty', subs) |> return

let rec infer :
    R.env -> ST.env -> program list -> (tprogram list * R.env, string) result =
 fun env letters -> function
  | [] -> Result.ok ([], env)
  | RecBind (name, expr) :: tls ->
      let infer_generalize =
        let* env, var_ty, var' = infer_pattern name in
        let* (expr' : texpr), (expr_ty : ty), subs =
          in_env env (infer_expr expr)
        in
        let var_ty' = SubstitableType.apply subs var_ty in
        let* subs = solver [ (var_ty', expr_ty) ] in
        let env' = SubstitableTypeEnv.apply subs env in
        let name'' = SubstitablePattern.apply subs var' in
        let expr' = SubstitableExpr.apply subs expr' in
        let* env'', metas = generalize env' in

        Option.fold metas
          ~some:(fun metas ->
            (RecBind (PTPoly (metas, name''), TPoly (metas, expr')), env''))
          ~none:(RecBind (name'', expr'), env'')
        |> return
      in
      let expr', letters' = run infer_generalize env letters in
      Result.bind expr' (fun (expr'', env'') ->
          infer (env'' @ env) letters' tls
          |> Result.map (fun (program, letters') ->
                 (expr'' :: program, letters')))
  | Bind (name, expr) :: tls ->
      let infer_generalize =
        let* (expr' : texpr), (expr_ty : ty), subs = infer_expr expr in

        let* env, var_ty, var' = infer_pattern name in
        let var_ty' = SubstitableType.apply subs var_ty in
        let* subs = solver [ (var_ty', expr_ty) ] in
        let env' = SubstitableTypeEnv.apply subs env in
        let name'' = SubstitablePattern.apply subs var' in
        let expr' = SubstitableExpr.apply subs expr' in
        let* env'', metas = generalize env' in

        Option.fold metas
          ~some:(fun metas ->
            (Bind (PTPoly (metas, name''), TPoly (metas, expr')), env''))
          ~none:(Bind (name'', expr'), env'')
        |> return
      in
      let expr', letters' = run infer_generalize env letters in
      Result.bind expr' (fun (expr'', env'') ->
          infer (env'' @ env) letters' tls
          |> Result.map (fun (program, letters') ->
                 (expr'' :: program, letters')))
  | Expr expr :: tls ->
      let expr', letters' = run (infer_expr expr) env letters in
      Result.bind expr' (fun (expr'', _, _) ->
          infer env letters' tls
          |> Result.map (fun (program, letters') ->
                 (Expr expr'' :: program, letters')))

let infer env = Result.map fst << infer env letters
