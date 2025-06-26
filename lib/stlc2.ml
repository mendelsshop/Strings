type term = Var of string | Lambda of string * term | App of term * term
type ty = TyVar of string | TyUnit | TyArrow of ty * ty

type typed_term =
  | TVar of string * ty
  | TLambda of string * ty * typed_term * ty
  | TApp of typed_term * typed_term * ty

type co = CEq of ty * ty

module Subst = Map.Make (String)

type subst = ty Subst.t

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

let sove_constraints _constraints = failwith "todo"
