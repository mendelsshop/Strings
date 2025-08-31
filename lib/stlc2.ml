type term =
  | Var of string
  | Lambda of string * term
  | App of term * term
  | Unit

type 't ty = TyVar of string | TyUnit | TyArrow of 't * 't
type 't co = CEq of 't * 't

let type_to_string to_string = function
  | TyVar x -> x
  | TyUnit -> "()"
  | TyArrow (x, y) -> to_string x ^ " -> " ^ to_string y

type 't typed_term =
  | TVar of string * 't
  | TLambda of string * 't * 't typed_term * 't
  | TApp of 't typed_term * 't typed_term * 't
  | TUnit of 't

let type_tag_to_string = function
  | TyVar _ -> "tyvar"
  | TyArrow _ -> "tyarrow"
  | TyUnit -> "tyunit"

type node_ty = 'a ty Union_find.elem as 'a

let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'

let node_type_to_string ty =
  (* TODO: figure out how to properly print recursive types *)
  let rec inner used ty =
    let root, `root node = Union_find.find_set ty in
    (List.assq_opt root used
    |> Option.fold
         ~some:(fun t () -> (t, [ ty ]))
         ~none:(fun () ->
           match node.data with
           | TyVar v -> (v, [])
           | TyUnit -> ("()", [])
           | TyArrow (x, y) ->
               let sym = gensym () in
               let x_string, used' = inner ((root, sym) :: used) x in
               let y_string, used'' = inner ((root, sym) :: used) y in
               let used' = used' @ used'' in
               let recursive_prefix =
                 if List.memq x used' then "recursive " ^ sym ^ ". " else ""
               in
               (recursive_prefix ^ x_string ^ " -> " ^ y_string, used')))
      ()
  in
  inner [] ty |> fst

let tterm_to_string type_to_string =
  let rec inner = function
    | TVar (v, _) -> v
    | TLambda (v, v_ty, typed_term, _) ->
        "(fun (" ^ v ^ ": " ^ type_to_string v_ty ^ ") -> " ^ inner typed_term
        ^ ")"
    | TApp (f, a, _) -> "[" ^ inner f ^ " " ^ inner a ^ "]"
    | TUnit _ -> "()"
  in
  inner

let rec generate_constraints env ty = function
  | Var v -> ([ CEq (List.assoc v env, ty) ], TVar (v, ty))
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
    | TyVar _, v | v, TyVar _ ->
        let _ = Union_find.union_with (fun _ _ -> v) s t in
        ()
    | _ -> ()

let unify = List.iter unify
