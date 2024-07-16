open Expr.Types
open Expr
open Monad
open Monad.ResultReaderOps

let in_env (name, ty) m =
  let scope env = (name, ty) :: env in
  R.local scope m

module Subst = Map.Make (String)

type subst = ty Subst.t

module type Substitable = sig
  type t

  val apply : subst -> t -> t
  val ftv : t -> MetaVariables.t
end

module SubstitableType : Substitable with type t = ty = struct
  type t = ty

  let rec apply subst = function
    | (TBool | TInt) as ty -> ty
    | TMeta meta as ty ->
        Subst.find_opt meta subst |> Option.fold ~none:ty ~some:(fun x -> x)
    | TArrow (t1, t2) -> TArrow (apply subst t1, apply subst t2)
    | TPoly (metas, ty) ->
        (*TODO: foldr*)
        let subst' = MetaVariables.fold Subst.remove metas subst in
        TPoly (metas, apply subst' ty)

  let rec ftv = function
    | TBool | TInt -> MetaVariables.empty
    | TMeta meta -> MetaVariables.singleton meta
    | TArrow (t1, t2) -> MetaVariables.union (ftv t1) (ftv t2)
    | TPoly (metas, ty) -> MetaVariables.diff (ftv ty) metas
end

module SubstitableConstraint : Substitable with type t = ty * ty = struct
  type t = ty * ty

  let apply subs (t1, t2) =
    (SubstitableType.apply subs t1, SubstitableType.apply subs t2)

  let ftv (t1, t2) =
    MetaVariables.union (SubstitableType.ftv t1) (SubstitableType.ftv t2)
end

module SubstitableA (S : Substitable) : Substitable with type t = S.t list =
struct
  type t = S.t list

  let apply = Stdlib.List.map << S.apply

  let ftv this =
    Stdlib.List.fold_right
      (MetaVariables.union << S.ftv)
      this MetaVariables.empty
end

module SubstitableTypeEnv : Substitable with type t = (string * ty) list =
struct
  type t = (string * ty) list

  module SubstitableTypes = SubstitableA (SubstitableType)

  let apply s env =
    Stdlib.List.map (fun (name, ty) -> (name, SubstitableType.apply s ty)) env

  let ftv env = Stdlib.List.map (fun (_, ty) -> ty) env |> SubstitableTypes.ftv
end

module SubstitableExpr : Substitable with type t = texpr = struct
  type t = texpr

  (*apply is rescursive so that all types are filled in in all sub expressions*)
  let rec apply subs = function
    | TVar (var, ty) -> TVar (var, SubstitableType.apply subs ty)
    | (TBoolean _ | TNumber _) as e -> e
    | TIf (cond, cons, alt, ty) ->
        TIf
          ( apply subs cond,
            apply subs cons,
            apply subs alt,
            SubstitableType.apply subs ty )
    | TLet (var, e1, e2, ty) ->
        TLet (var, apply subs e1, apply subs e2, SubstitableType.apply subs ty)
    | TLambda (var, arg_ty, abs, ty) ->
        TLambda
          ( var,
            SubstitableType.apply subs arg_ty,
            apply subs abs,
            SubstitableType.apply subs ty )
    | TApplication (abs, arg, ty) ->
        TApplication
          (apply subs abs, apply subs arg, SubstitableType.apply subs ty)
    | TPoly (metas, expr) ->
        let subst' = MetaVariables.fold Subst.remove metas subs in
        TPoly (metas, apply subst' expr)

  let ftv expr = type_of expr |> SubstitableType.ftv
end

let occurs_check a t = SubstitableType.ftv t |> MetaVariables.mem a
let compose s1 s2 = Subst.union (fun _ fst _ -> Some fst) s1 s2

let new_meta =
  let* letters = ST.get () |> R.lift |> lift in
  let* letter, letters' =
    Stdlib.Option.fold
      ~none:(fail "ran out of fresh type variables")
      ~some:(fun (letter, letters') -> (TMeta letter, letters') |> return)
      (Stdlib.Seq.uncons letters)
  in
  let* _ = ST.put letters' |> R.lift |> lift in
  return letter

let instantiate : ty -> ty ResultReader.t = function
  | TPoly (metas, ty) ->
      let* subs =
        MetaVariables.to_seq metas |> Stdlib.List.of_seq
        |> List.map ~f:(fun meta ->
               let* ty = new_meta in
               return (meta, ty))
      in
      let subs' = subs |> Stdlib.List.to_seq |> Subst.of_seq in
      SubstitableType.apply subs' ty |> return
  | ty -> return ty

let rec unify t1 t2 =
  match (t1, t2) with
  | _, _ when t1 = t2 -> return Subst.empty
  | TMeta t, ty when occurs_check t ty -> fail ""
  | ty, TMeta t when occurs_check t ty -> fail ""
  | TMeta t, ty | ty, TMeta t -> Subst.singleton t ty |> return
  | TArrow (t1, t2), TArrow (t1', t2') ->
      let* subs = unify t1 t1' in
      let* subs' =
        unify (SubstitableType.apply subs t2) (SubstitableType.apply subs t2')
      in
      compose subs subs' |> return
  | _ -> fail "unification error"

let generalize ty =
  let ty_ftv = SubstitableType.ftv ty in
  let get_env = R.read () |> lift in
  let* env = get_env in
  let env_ftv = SubstitableTypeEnv.ftv env in
  MetaVariables.diff ty_ftv env_ftv |> return

let run e env = (run e |> R.run) env |> ST.run
let run_with_default e : ('a, string) result = run e [] letters |> fst
