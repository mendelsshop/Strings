type term = TVar of string | TLambda of string * term | TApp of term * term
type ty = TyVar of string | TyUnit | TyArrow of ty * ty

(* co means constraint (which is a reserved keyword in ocaml *)
type co =
  | CTrue
  | CFalse
  | CEq of ty * ty
  | CAnd of co * co
  | CExist of string * co
  | CDef of string * ty * co

let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'

let exist c =
  let a = gensym () in
  CExist (a, c a)

let rec generate_constraints ty = function
  | TVar t -> CEq (TyVar t, ty)
  | TLambda (x, t) ->
      exist (fun a1 ->
          exist (fun a2 ->
              CAnd
                ( CDef (x, TyVar a1, generate_constraints (TyVar a2) t),
                  CEq (TyArrow (TyVar a1, TyVar a2), ty) )))
  | TApp (f, x) ->
      exist (fun a1 ->
          CAnd
            ( generate_constraints (TyArrow (TyVar a1, ty)) f,
              generate_constraints (TyVar a1) x ))
