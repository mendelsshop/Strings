open Expr.Types
open Expr
open Monad
open Monad.ResultReaderOps

let in_env new_env m =
  let scope env = new_env @ env in
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
    | TTuple (t1, t2) -> TTuple (apply subst t1, apply subst t2)
    | TPoly (metas, ty) ->
        (*TODO: foldr*)
        let subst' = MetaVariables.fold Subst.remove metas subst in
        TPoly (metas, apply subst' ty)
    | TRowEmpty -> TRowEmpty
    | TRecord row -> TRecord (apply subst row)
    | TRowExtend (label, ty, row) ->
        TRowExtend (label, apply subst ty, apply subst row)

  let rec ftv = function
    | TBool | TInt | TRowEmpty -> MetaVariables.empty
    | TMeta meta -> MetaVariables.singleton meta
    | TRecord row -> ftv row
    | TRowExtend (_, ty, row) -> MetaVariables.union (ftv ty) (ftv row)
    | TArrow (t1, t2) -> MetaVariables.union (ftv t1) (ftv t2)
    | TTuple (t1, t2) -> MetaVariables.union (ftv t1) (ftv t2)
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

module SubstitablePattern : Substitable with type t = tpattern = struct
  type t = tpattern

  let rec apply subs = function
    | PTVar (var, ty) -> PTVar (var, SubstitableType.apply subs ty)
    | (PTBoolean _ | PTNumber _) as e -> e
    | PTTuple (e1, e2, ty) ->
        PTTuple (apply subs e1, apply subs e2, SubstitableType.apply subs ty)
    | PTWildcard ty -> PTWildcard (SubstitableType.apply subs ty)
    | PTPoly (metas, pat) ->
        let subst' = MetaVariables.fold Subst.remove metas subs in
        PTPoly (metas, apply subst' pat)
    | PTRecord (row, ty) ->
        PTRecord (Row.map (apply subs) row, SubstitableType.apply subs ty)

  let ftv pattern = type_of_pattern pattern |> SubstitableType.ftv
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
        TLet
          ( SubstitablePattern.apply subs var,
            apply subs e1,
            apply subs e2,
            SubstitableType.apply subs ty )
    | TLambda (var, abs, ty) ->
        TLambda
          ( SubstitablePattern.apply subs var,
            apply subs abs,
            SubstitableType.apply subs ty )
    | TApplication (abs, arg, ty) ->
        TApplication
          (apply subs abs, apply subs arg, SubstitableType.apply subs ty)
    | TTuple (e1, e2, ty) ->
        TTuple (apply subs e1, apply subs e2, SubstitableType.apply subs ty)
    | TPoly (metas, expr) ->
        let subst' = MetaVariables.fold Subst.remove metas subs in
        TPoly (metas, apply subst' expr)
    | TRecord (row, ty) ->
        TRecord (Row.map (apply subs) row, SubstitableType.apply subs ty)
    | TRecordAcces (record, label, ty) ->
        TRecordAcces (apply subs record, label, SubstitableType.apply subs ty)

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
  let open Types in
  let rewrite_row _label _row2 = failwith "record not implemented" in
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
  | TTuple (t1, t2), TTuple (t1', t2') ->
      let* subs = unify t1 t1' in
      let* subs' =
        unify (SubstitableType.apply subs t2) (SubstitableType.apply subs t2')
      in
      compose subs subs' |> return
  | TRecord (TRowExtend _ as r1), TRecord (TRowExtend _ as r2) -> unify r1 r2
  (*TODO: can we be a bit more general about what row2 is?*)
  | TRowExtend (label, ty, rest_row), (TRowExtend _ as row2) ->
      let* row2_ty, row2_rest_row, subs = rewrite_row label row2 in
      (*TODO: termination check *)
      (*if Subst.exists (fun sub sub_ty -> failwith "") subs then fail ""*)
      (*else*)
      let* subs' =
        unify
          (SubstitableType.apply subs ty)
          (SubstitableType.apply subs row2_ty)
      in
      let subs = compose subs' subs in
      let* subs' =
        unify
          (SubstitableType.apply subs rest_row)
          (SubstitableType.apply subs row2_rest_row)
      in
      compose subs subs' |> return
  | _ ->
      "unification error " ^ type_to_string t1 ^ " " ^ type_to_string t2 |> fail

let generalize ty =
  let ty_ftv = SubstitableType.ftv ty in
  let get_env = R.read () |> lift in
  let* env = get_env in
  let env_ftv = SubstitableTypeEnv.ftv env in
  MetaVariables.diff ty_ftv env_ftv |> return

let run e env = (run e |> R.run) env |> ST.run
let run_with_default e : ('a, string) result = run e [] letters |> fst
