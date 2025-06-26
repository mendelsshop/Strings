type term = Var of string | Lambda of string * term | App of term * term
type ty = TyVar of string | TyUnit | TyArrow of ty * ty

let rec type_to_string = function
  | TyVar x -> x
  | TyUnit -> "()"
  | TyArrow (x, y) -> type_to_string x ^ " -> " ^ type_to_string y

module Subst = Map.Make (String)
module StringSet = Set.Make (String)

let rec type_ftv = function
  | TyVar x -> StringSet.singleton x
  | TyUnit -> StringSet.empty
  | TyArrow (x, y) -> StringSet.union (type_ftv x) (type_ftv y)

type typed_term =
  | TVar of string * ty
  | TLambda of string * ty * typed_term * ty
  | TApp of typed_term * typed_term * ty

let rec tterm_to_string = function
  | TVar (v, ty) -> "(" ^ v ^ ": " ^ type_to_string ty ^ ")"
  | TLambda (v, v_ty, typed_term, ty) ->
      "((fun " ^ v ^ ": " ^ type_to_string v_ty ^ " -> "
      ^ tterm_to_string typed_term ^ ")" ^ ": " ^ type_to_string ty ^ ")"
  | TApp (f, a, ty) ->
      "(" ^ tterm_to_string f ^ " " ^ tterm_to_string a ^ ": "
      ^ type_to_string ty ^ ")"

type co = CEq of ty * ty

let constraint_to_string = function
  | CEq (t1, t2) -> type_to_string t1 ^ "~= " ^ type_to_string t2

let constraints_to_string ts =
  "[\n" ^ (ts |> List.map constraint_to_string |> String.concat "\n") ^ "\n]"

type subst = ty Subst.t

let subst_to_string s =
  "[\n"
  ^ (s |> Subst.to_list
    |> List.map (fun (k, v) -> k ^ ": " ^ type_to_string v)
    |> String.concat "\n")
  ^ "\n]"

let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'

let rec generate_constraints ty env = function
  | Var t -> ([ CEq (List.assoc t env, ty) ], TVar (t, ty))
  | Lambda (x, t) ->
      let a1 = gensym () in
      let a2 = gensym () in
      let c, t' = generate_constraints (TyVar a2) ((x, TyVar a1) :: env) t in
      ( CEq (TyArrow (TyVar a1, TyVar a2), ty) :: c,
        TLambda (x, TyVar a1, t', ty) )
  | App (f, x) ->
      let a1 = gensym () in
      let c, f' = generate_constraints (TyArrow (TyVar a1, ty)) env f in
      let c', x' = generate_constraints (TyVar a1) env x in
      (c @ c', TApp (f', x', ty))

let rec apply_subst_ty subst = function
  | TyVar v -> Subst.find_opt v subst |> Option.value ~default:(TyVar v)
  | TyArrow (p, r) -> TyArrow (apply_subst_ty subst p, apply_subst_ty subst r)
  | TyUnit -> TyUnit

let rec apply_subst_tterm subst = function
  | TVar (v, ty) -> TVar (v, apply_subst_ty subst ty)
  | TLambda (v, v_ty, b, ty) ->
      TLambda
        ( v,
          apply_subst_ty subst v_ty,
          apply_subst_tterm subst b,
          apply_subst_ty subst ty )
  | TApp (f, a, ty) ->
      TApp
        ( apply_subst_tterm subst f,
          apply_subst_tterm subst a,
          apply_subst_ty subst ty )

let apply_subst_subst subst on_subst = Subst.map (apply_subst_ty subst) on_subst

(* TODO: make sure correct order *)
let combose_subst subst subst' =
  Subst.union (fun _ a _ -> Some a) (apply_subst_subst subst subst') subst

let rec solve_constraint = function
  | CEq (t1, t2) when t1 = t2 -> Subst.empty
  | CEq (TyVar u, t1) | CEq (t1, TyVar u) ->
      if StringSet.mem u (type_ftv t1) then failwith "occurs check"
      else Subst.singleton u t1
  | CEq (TyArrow (tp1, tr1), TyArrow (tp2, tr2)) ->
      let subst = solve_constraint (CEq (tp1, tp2)) in
      let subst' =
        solve_constraint
          (CEq (apply_subst_ty subst tr1, apply_subst_ty subst tr2))
      in
      combose_subst subst subst'
  | _ -> failwith "error"

let rec solve_constraints = function
  | [] -> Subst.empty
  | cs :: constraints ->
      let subst = solve_constraint cs in
      let constraints' =
        List.map
          (fun (CEq (x, y)) ->
            CEq (apply_subst_ty subst x, apply_subst_ty subst y))
          constraints
      in
      let subst' = solve_constraints constraints' in
      combose_subst subst' subst
