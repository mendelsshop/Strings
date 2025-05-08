type term = TVar of string | TLambda of string * term | TApp of term * term
type ty = TyVar of string | TyUnit | TyArrow of ty * ty

let rec type_to_string = function
  | TyVar x -> x
  | TyUnit -> "()"
  | TyArrow (x, y) -> type_to_string x ^ " -> " ^ type_to_string y

module Variables = Set.Make (String)

(* maybe look at wand algorithim for stlc *)
(* co means constraint (which is a reserved keyword in ocaml *)
type co =
  | CTrue
  | CFalse
  | CEq of ty * ty
  | CAnd of co * co
  | CExist of Variables.t * co
  | CDef of string * ty * co

type co_u =
  | UTrue
  | UFalse
  | UMulti of ty list
  | UAnd of co_u * co_u
  | UExist of Variables.t * co_u

let rec u_constraint_to_string = function
  | UTrue -> "true"
  | UFalse -> "false"
  | UMulti ts -> ts |> List.map type_to_string |> String.concat " = "
  | UAnd (c1, c2) ->
      "and (" ^ u_constraint_to_string c1 ^ ") (" ^ u_constraint_to_string c2
      ^ ")"
  | UExist (x, c) ->
      "∃"
      ^ (x |> Variables.to_list |> String.concat ",")
      ^ ".(" ^ u_constraint_to_string c

let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'

let uexist c =
  let a = gensym () in
  UExist (Variables.singleton a, c a)

let uexist2 c =
  let a = gensym () in
  let a' = gensym () in
  UExist (Variables.of_list [ a; a' ], c a a')

let exist c =
  let a = gensym () in
  CExist (Variables.singleton a, c a)

let exist2 c =
  let a = gensym () in
  let a' = gensym () in
  CExist (Variables.of_list [ a; a' ], c a a')

let rec ugenerate_constraints ty env = function
  | TVar t -> UMulti [ List.assoc t env; ty ]
  | TLambda (x, t) ->
      uexist2 (fun a1 a2 ->
          UAnd
            ( ugenerate_constraints (TyVar a2) ((x, TyVar a1) :: env) t,
              UMulti [ TyArrow (TyVar a1, TyVar a2); ty ] ))
  | TApp (f, x) ->
      uexist (fun a1 ->
          UAnd
            ( ugenerate_constraints (TyArrow (TyVar a1, ty)) env f,
              ugenerate_constraints (TyVar a1) env x ))

let rec generate_constraints ty = function
  | TVar t -> CEq (TyVar t, ty)
  | TLambda (x, t) ->
      exist2 (fun a1 a2 ->
          CAnd
            ( CDef (x, TyVar a1, generate_constraints (TyVar a2) t),
              CEq (TyArrow (TyVar a1, TyVar a2), ty) ))
  | TApp (f, x) ->
      exist (fun a1 ->
          CAnd
            ( generate_constraints (TyArrow (TyVar a1, ty)) f,
              generate_constraints (TyVar a1) x ))

let rec type_ftv = function
  | TyVar x -> Variables.singleton x
  | TyUnit -> Variables.empty
  | TyArrow (t1, t2) -> Variables.union (type_ftv t1) (type_ftv t2)

let rec uconstraint_ftv = function
  | UTrue -> Variables.empty
  | UFalse -> Variables.empty
  | UMulti c ->
      c |> List.map type_ftv |> List.fold_left Variables.union Variables.empty
  | UAnd (c1, c2) -> Variables.union (uconstraint_ftv c1) (uconstraint_ftv c2)
  | UExist (x, c) -> Variables.diff (uconstraint_ftv c) x

let rec constraint_ftv = function
  | CTrue -> Variables.empty
  | CFalse -> Variables.empty
  | CEq (t1, t2) -> Variables.union (type_ftv t1) (type_ftv t2)
  | CAnd (c1, c2) -> Variables.union (constraint_ftv c1) (constraint_ftv c2)
  | CExist (x, c) -> Variables.diff (constraint_ftv c) x
  | CDef (_, ty, c) -> Variables.union (type_ftv ty) (constraint_ftv c)

let rec fusion vs prev default = function
  | TyVar x :: xs when List.mem x vs -> UMulti (xs @ prev)
  | x :: xs -> fusion vs (x :: prev) default xs
  | [] -> default

let top_level_ty_vars =
  List.filter_map (function TyVar t -> Some t | _ -> None)

let not_var = function TyVar _ -> false | _ -> true

(* idea is to rewrite untill it looks like substition (i.e. exist at top with bunch of ands of multi equations with first item being type variable bound by exist) aka normalized constraint *)
(* maybe just do normal unification *)
(* or at least only have one constraint type  *)
let rec unfiy = function
  | UAnd (UExist (x, c1), c2)
    when let ftv = uconstraint_ftv c2 in
         Variables.equal (Variables.diff ftv x) ftv ->
      UExist (x, UAnd (c1, c2)) |> unfiy
  | UAnd (c2, UExist (x, c1))
    when let ftv = uconstraint_ftv c2 in
         Variables.equal (Variables.diff ftv x) ftv ->
      UExist (x, UAnd (c1, c2)) |> unfiy
  (* TODO: i am assuming right now for multi equtions that order does matter but it probably doesn't *)
  | UAnd (UMulti e, UMulti e') as c when not (Variables.disjoint (top_level_ty_vars  e' |> Variables.of_list) (top_level_ty_vars  e |> Variables.of_list))  -> fusion (top_level_ty_vars e') e' c e |> unfiy
  (* | UAnd (UMulti (TyVar x :: e), UMulti (TyVar x' :: e')) when x = x' -> *)
  (*     UMulti ((TyVar x :: e) @ e') |> unfiy *)
  | UMulti (TyArrow (TyVar a, TyVar b) :: TyArrow (a', b') :: e) ->
      UAnd
        ( UMulti [ TyVar a; a' ],
          UAnd (UMulti [ TyVar b; b' ], UMulti (TyArrow (a', b') :: e)) )
      |> unfiy
  | UMulti (TyArrow (a, b) :: e) when not_var a ->
      uexist (fun a' ->
          UAnd (UMulti [ TyVar a'; a ], UMulti (TyArrow (TyVar a', b) :: e)))
      |> unfiy
  | UAnd (c, UTrue) | UAnd (UTrue, c) -> c |> unfiy
  | UExist (x, UExist (x', c)) -> UExist (Variables.union x x', c) |> unfiy
  (* recurse rules *)
  | UExist (x, c) ->
      let c' = unfiy c in
      UExist (x, c') |> if c = c' then Fun.id else unfiy
  | UAnd (c1, c2) ->
      let c1' = unfiy c1 in
      let c2' = unfiy c2 in
      UAnd (c1', c2') |> if c1 = c1' && c2 = c2' then Fun.id else unfiy
  | UMulti [ _ ] -> UTrue
  (* TODO: maybe occurs check *)
  | UFalse -> UFalse
  | x -> x (* Should this fail if cannot reduce *)
