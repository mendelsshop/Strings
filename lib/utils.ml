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

  val to_string : t -> string
  val apply : subst -> t -> t
  val ftv : t -> MetaVariables.t
end

module SubstitableType : Substitable with type t = ty = struct
  type t = ty

  let to_string : ty -> string = type_to_string

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
    | TMu (meta, ty) ->
        (*TODO: foldr*)
        let subst' = Subst.remove meta subst in
        TMu (meta, apply subst' ty)
    | TRowEmpty -> TRowEmpty
    | TRecord row -> TRecord (apply subst row)
    | TVariant row -> TVariant (apply subst row)
    | TRowExtend (label, ty, row) ->
        TRowExtend (label, apply subst ty, apply subst row)

  let rec ftv = function
    | TBool | TInt | TRowEmpty -> MetaVariables.empty
    | TMeta meta -> MetaVariables.singleton meta
    | TRecord row -> ftv row
    | TVariant row -> ftv row
    | TRowExtend (_, ty, row) -> MetaVariables.union (ftv ty) (ftv row)
    | TArrow (t1, t2) -> MetaVariables.union (ftv t1) (ftv t2)
    | TTuple (t1, t2) -> MetaVariables.union (ftv t1) (ftv t2)
    | TPoly (metas, ty) -> MetaVariables.diff (ftv ty) metas
    | TMu (meta, ty) ->
        (* TODO: just remove meta from ftv of ty *)
        MetaVariables.diff (ftv ty) (MetaVariables.singleton meta)
end

module SubstitableConstraint : Substitable with type t = ty * ty = struct
  type t = ty * ty

  let to_string (ty, ty') = type_to_string ty ^ "~=" ^ type_to_string ty'

  let apply subs (t1, t2) =
    (SubstitableType.apply subs t1, SubstitableType.apply subs t2)

  let ftv (t1, t2) =
    MetaVariables.union (SubstitableType.ftv t1) (SubstitableType.ftv t2)
end

module SubstitableA (S : Substitable) : Substitable with type t = S.t list =
struct
  type t = S.t list

  let to_string l = l |> Stdlib.List.map S.to_string |> String.concat ", "
  let apply subs s = Stdlib.List.map (fun x -> S.apply subs x) s

  let ftv this =
    Stdlib.List.fold_right
      (MetaVariables.union << S.ftv)
      this MetaVariables.empty
end

module SubstitableTypeEnv : Substitable with type t = (string * ty) list =
struct
  type t = (string * ty) list

  let to_string l =
    l
    |> Stdlib.List.map (fun (b, s) -> b ^ ": " ^ SubstitableType.to_string s)
    |> String.concat ", "

  module SubstitableTypes = SubstitableA (SubstitableType)

  let apply s env =
    Stdlib.List.map (fun (name, ty) -> (name, SubstitableType.apply s ty)) env

  let ftv env = Stdlib.List.map (fun (_, ty) -> ty) env |> SubstitableTypes.ftv
end

module SubstitablePattern : Substitable with type t = tpattern = struct
  type t = tpattern

  let to_string = tpattern_to_string

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
        PTRecord
          ( Stdlib.List.map (fun (field, ty) -> (field, apply subs ty)) row,
            SubstitableType.apply subs ty )
    | PTConstructor (name, row, ty) ->
        PTConstructor (name, apply subs row, SubstitableType.apply subs ty)

  let ftv pattern = type_of_pattern pattern |> SubstitableType.ftv
end

module SubstitableExpr : Substitable with type t = texpr = struct
  type t = texpr

  let to_string = texpr_to_string

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
    | TLetRec (var, e1, e2, ty) ->
        TLetRec
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
        TRecord
          ( Stdlib.List.map (fun (field, ty) -> (field, apply subs ty)) row,
            SubstitableType.apply subs ty )
    | TRecordExtend (expr, row, ty) ->
        TRecordExtend
          ( apply subs expr,
            Stdlib.List.map (fun (field, ty) -> (field, apply subs ty)) row,
            SubstitableType.apply subs ty )
    | TConstructor (name, row, ty) ->
        TConstructor (name, (apply subs) row, SubstitableType.apply subs ty)
    | TRecordAcces (record, label, ty) ->
        TRecordAcces (apply subs record, label, SubstitableType.apply subs ty)
    | TMatch (expr, cases, ty) ->
        TMatch
          ( apply subs expr,
            Stdlib.List.map
              (fun (pat, case) ->
                (SubstitablePattern.apply subs pat, apply subs case))
              cases,
            SubstitableType.apply subs ty )

  let ftv expr = type_of expr |> SubstitableType.ftv
end

let occurs_check a t = SubstitableType.ftv t |> MetaVariables.mem a
let compose s1 s2 = Subst.union (fun _ fst _ -> Some fst) s1 s2

let new_meta =
  let* letters = ST.get () |> R.lift |> lift in
  let* letter, letters' =
    Stdlib.Option.fold
      ~none:(fail "Ran out of fresh type variables.")
      ~some:(fun (letter, letters') -> (letter, letters') |> return)
      (Stdlib.Seq.uncons letters)
  in
  let* _ = ST.put letters' |> R.lift |> lift in
  return letter

let muify v ty =
  let* v' = new_meta in
  let rec inner = function
    | TMeta n when v = n -> TMeta v'
    | TTuple (l, r) -> TTuple (inner l, inner r)
    | TArrow (l, r) -> TArrow (inner l, inner r)
    | TRecord ty -> TRecord (inner ty)
    | TVariant ty -> TVariant (inner ty)
    | TRowExtend (v, ty, rest) -> TRowExtend (v, inner ty, inner rest)
    | ty -> ty
  in
  return (TMu (v', inner ty))

let new_meta = map new_meta ~f:(fun t -> TMeta t)

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
  let rec rewrite_row new_label = function
    | TRowEmpty -> "Cannot add label `" ^ new_label ^ "` to row." |> fail
    | TRowExtend (label, field_ty, row_tail) when new_label = label ->
        return (field_ty, row_tail, Subst.empty)
    | TRowExtend (label, field_ty, TMeta m) ->
        let* beta = new_meta in
        let* gamma = new_meta in
        ( gamma,
          TRowExtend (label, field_ty, beta),
          Subst.singleton m (TRowExtend (new_label, gamma, beta)) )
        |> return
    | TRowExtend (label, field_ty, row_tail) ->
        let* field_ty', row_tail', subs = rewrite_row new_label row_tail in
        if row_tail = row_tail' then print_endline "same";
        return (field_ty', TRowExtend (label, field_ty, row_tail'), subs)
    | ty ->
        type_to_string ty
        ^ " is not a row, so it cannot be extended with label `" ^ new_label
        ^ "`."
        |> fail
  in
  type_to_string t1 ^ " ~= " ^ type_to_string t2 |> print_endline;
  match (t1, t2) with
  | _, _ when t1 = t2 -> return Subst.empty
  | TMeta t, ty | ty, TMeta t ->
      (* TODO: make sure its only muing types that are for record/variants *)
      if occurs_check t ty then
        let* mu = muify t ty in
        Subst.singleton t mu |> return
      (* "Occurs check fails, for type " ^ t ^ " in type " ^ type_to_string ty *)
      (* ^ "." *)
      (* |> fail *)
        else Subst.singleton t ty |> return
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
  | TRecord r1, TRecord r2 -> unify r1 r2
  | TVariant r1, TVariant r2 -> unify r1 r2
  (*TODO: can we be a bit more general about what row2 is?*)
  | TRowExtend (label1, field_ty1, row_tail1), (TRowExtend _ as row_tail2) ->
      let* field_ty2, row_tail2, subs = rewrite_row label1 row_tail2 in
      (* row_tail row_tail1 |> Option.value ~default:"bll" |> print_endline; *)
      (* "subs " *)
      (* ^ (subs |> Subst.to_list *)
      (*   |> Stdlib.List.map (fun (name, ty) -> name ^ " = " ^ type_to_string ty) *)
      (*   |> String.concat ", ") *)
      (* |> print_endline; *)
      if
        row_tail row_tail1
        |> Option.fold ~none:false ~some:(fun tv -> Subst.mem tv subs)
      then
        (* TODO: mu type here? *)
        fail ("recursive row " ^ type_to_string t1 ^ " and " ^ type_to_string t2)
      else
        let* subs' =
          unify
            (SubstitableType.apply subs field_ty1)
            (SubstitableType.apply subs field_ty2)
        in
        let subs = compose subs' subs in
        let* subs' =
          unify
            (SubstitableType.apply subs row_tail1)
            (SubstitableType.apply subs row_tail2)
        in
        compose subs subs' |> return
  | _ ->
      "Unification error " ^ type_to_string t1 ^ " and " ^ type_to_string t2
      ^ "."
      |> fail

let generalize ty =
  let ty_ftv = SubstitableType.ftv ty in
  let get_env = R.read () |> lift in
  let* env = get_env in
  let env_ftv = SubstitableTypeEnv.ftv env in
  MetaVariables.diff ty_ftv env_ftv |> return

let run e env = (run e |> R.run) env |> ST.run
let run_with_default e : ('a, string) result = run e [] letters |> fst
