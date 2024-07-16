open Expr.Types
open Expr
open Monad
open Monad.ResultReaderOps
open Utils

let rec solver = function
  | [] -> return Subst.empty
  | (t1, t2) :: cs' ->
      let* subs = unify t1 t2 in
      let open SubstitableA (SubstitableConstraint) in
      let* subs' = apply subs cs' |> solver in
      compose subs subs' |> return

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
        let* subs = solver cs in
        let e1'' = SubstitableExpr.apply subs e1' in
        let e1_ty' = SubstitableType.apply subs e1_ty in
        let* metas = generalize e1_ty' in
        let* cs', e2_ty, e2' =
          in_env (var, TPoly (metas, e1_ty')) (infer_inner e2)
        in
        return (cs @ cs', e2_ty, TLet (var, TPoly (metas, e1''), e2', e2_ty))
    | Lambda (var, abs) ->
        let* arg_ty = new_meta in
        let* cs, abs_ty, abs' = in_env (var, arg_ty) (infer_inner abs) in
        let ty = TArrow (arg_ty, abs_ty) in
        return (cs, ty, TLambda (var, arg_ty, abs', ty))
    | Application (abs, arg) ->
        let* cs, abs_ty, abs' = infer_inner abs in
        let* cs', arg_ty, arg' = infer_inner arg in
        let* ret_ty = new_meta in
        return
          ( ((abs_ty, TArrow (arg_ty, ret_ty)) :: cs) @ cs',
            ret_ty,
            TApplication (abs', arg', ret_ty) )
  in
  let* cs, ty, expr' = infer_inner expr in
  let* subs = solver cs in
  (SubstitableExpr.apply subs expr', ty) |> return

let rec infer :
    R.env -> ST.env -> program list -> (tprogram list * R.env, string) result =
 fun env letters -> function
  | [] -> Result.ok ([], env)
  | Bind (name, expr) :: tls ->
      let infer_generalize =
        let* (expr' : texpr), (expr_ty : ty) = infer_expr expr in
        let* metas = generalize expr_ty in
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
