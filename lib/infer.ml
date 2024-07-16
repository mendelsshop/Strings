open Expr.Types
open Expr
open Utils
open Monad
open Monad.ResultReaderOps

let infer expr =
  let rec infer_inner expr =
    match expr with
    | Var x ->
        x |> get
        |> bind ~f:(fun ty ->
               let* ty' = instantiate ty in
               return (Subst.empty, ty', TVar (x, ty')))
    | Lambda ((var : string), abs) ->
        let* arg_ty = new_meta in
        let* subs, abs_ty, abs' = in_env (var, arg_ty) (infer_inner abs) in
        let arg_ty' = SubstitableType.apply subs arg_ty in
        let ty = TArrow (arg_ty', abs_ty) in
        return (subs, ty, TLambda (var, arg_ty', abs', ty))
    | Application (abs, arg) ->
        let* subs, abs_ty, abs' = infer_inner abs in
        R.local
          (SubstitableTypeEnv.apply subs)
          (let* subs', arg_ty, arg' = infer_inner arg and* meta = new_meta in
           let abs_ty' = SubstitableType.apply subs' abs_ty in
           let* v = unify abs_ty' (TArrow (arg_ty, meta)) in
           let meta' = SubstitableType.apply v arg_ty in
           let subs''' = (compose subs << compose subs') v in
           return (subs''', meta', TApplication (abs', arg', meta')))
    | Let (var, e1, e2) ->
        let* subs, e1_ty, e1' = infer_inner e1 in
        R.local
          (SubstitableTypeEnv.apply subs)
          (let* free_variables = e1_ty |> generalize in

           let* subs', e2_ty, e2' =
             in_env (var, TPoly (free_variables, e1_ty)) (infer_inner e2)
           in
           let subs'' = compose subs subs' in
           return
             (subs'', e2_ty, TLet (var, TPoly (free_variables, e1'), e2', e2_ty)))
    | Boolean b -> return (Subst.empty, TBool, TBoolean (b, TBool))
    | Number n -> return (Subst.empty, TInt, TNumber (n, TInt))
    | If (cond, cons, alt) ->
        let* subs, cond_ty, cond' = infer_inner cond in
        let* subs', cons_ty, cons' = infer_inner cons in
        let* subs'', alt_ty, alt' = infer_inner alt in
        let* v = unify cond_ty TBool in
        let cons_ty' = SubstitableType.apply (compose subs v) cons_ty in
        let alt_ty' = SubstitableType.apply (compose subs v) alt_ty in
        let* v' = unify cons_ty' alt_ty' in
        let cons_ty'' = SubstitableType.apply v' cons_ty' in
        let subs''' =
          (compose subs << compose subs' << compose subs'' << compose v) v'
        in
        return (subs''', cons_ty', TIf (cond', cons', alt', cons_ty''))
  in
  let* subs, ty, expr' = infer_inner expr in
  (SubstitableExpr.apply subs expr', ty) |> return

let infer_many = List.map ~f:(map ~f:fst << infer)
