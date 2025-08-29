type term =
  | Var of string
  | Lambda of string * term
  | App of term * term
  | Unit

type 't ty = TyVar of string | TyUnit | TyArrow of 't * 't
type 't co = CEq of 't ty Union_find.elem * 't ty Union_find.elem

type 't typed_term =
  | TVar of string * 't
  | TLambda of string * 't * 't typed_term * 't
  | TApp of 't typed_term * 't typed_term * 't
  | TUnit of 't

let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'

let rec generate_constraints env ty = function
  | Var v -> ([ CEq (ty, List.assoc v env) ], TVar (v, ty))
  | Unit -> ([ CEq (ty, Union_find.make TyUnit) ], TUnit ty)
  | App (f, x) ->
      let a1 = Union_find.make (TyVar (gensym ())) in

      let c, f' =
        generate_constraints env (Union_find.make (TyArrow (a1, ty))) f
      in
      let c', x' = generate_constraints env a1 x in
      (c @ c', TApp (f', x', ty))
  | Lambda (x, t) ->
      let a1 = Union_find.make (TyVar (gensym ())) in
      let a2 = Union_find.make (TyVar (gensym ())) in

      let c, t' = generate_constraints ((x, a1) :: env) a2 t in

      ( CEq (Union_find.make (TyArrow (a1, a2)), ty) :: c,
        TLambda (x, a1, t', ty) )

let rec unify (CEq (s, t)) =
  let s, `root s_data = Union_find.find_set s in
  let t, `root t_data = Union_find.find_set t in
  if s == t then ()
  else
    match (s_data.data, t_data.data) with
    | TyArrow (s1, s2), TyArrow (t1, t2) ->
        unify (CEq (s1, t1));
        unify (CEq (s2, t2))
    | TyUnit, TyUnit -> ()
    | TyVar _, _ | _, TyVar _ ->
        let _ = Union_find.union s t in
        ()
    | _ -> ()
