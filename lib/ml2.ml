type term =
  | Var of string
  | Lambda of string * term
  | App of term * term
  | Let of string * term * term
  | Unit

type 't ty_f = TyVar of string | TyUnit | TyArrow of 't * 't

let type_to_string to_string = function
  | TyVar x -> x
  | TyUnit -> "()"
  | TyArrow (x, y) -> to_string x ^ " -> " ^ to_string y

module Subst = Map.Make (String)
module StringSet = Set.Make (String)

type 't typed_term =
  | TVar of string * 't
  | TLambda of string * 't * 't typed_term * 't
  | TApp of 't typed_term * 't typed_term * 't
  | TUnit of 't
  | TLet of string * 't * 't typed_term * 't typed_term * 't

type ty = 'a ty_f Union_find.elem as 'a

let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'

let type_to_string ty =
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
    | TLet (v, v_ty, e1, e2, _) ->
        "let " ^ v ^ ": " ^ type_to_string v_ty ^ " = " ^ inner e1 ^ " in "
        ^ inner e2
  in
  inner

(* do we need CExist: quote from tapl "Furthermore, we must bind them existentially, because we *)
(* intend the onstraint solver to choose some appropriate value for them" *)
type 't co =
  | CExist of string list * 't co list
  | CEq of 't * 't
  | CInstance of string * 't
  | CLet of string * 't scheme * 't co list

and 't scheme = ForAll of string list * 't co list * 't

let rec constraint_to_string = function
  | CEq (t1, t2) -> type_to_string t1 ^ "~= " ^ type_to_string t2
  | CInstance (var, ty) -> var ^ " instanceof " ^ type_to_string ty
  | CLet (var, ForAll (vars, cos, ty), cos') ->
      "let " ^ var ^ " :(ForAll " ^ String.concat ", " vars ^ " "
      ^ constraints_to_string cos ^ "." ^ type_to_string ty ^ ") in"
      ^ constraints_to_string cos'
  | CExist (vars, cos) ->
      "Exists " ^ String.concat ", " vars ^ " " ^ "."
      ^ constraints_to_string cos

and constraints_to_string ts =
  "[" ^ (ts |> List.map constraint_to_string |> String.concat ", ") ^ "]"

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

let rec generate_constraints ty = function
  | Unit -> ([ CEq (ty, Union_find.make TyUnit) ], TUnit ty)
  | Var t -> ([ CInstance (t, ty) ], TVar (t, ty))
  | App (f, x) ->
      let a1 = Union_find.make (TyVar (gensym ())) in
      let c, f' = generate_constraints (Union_find.make (TyArrow (a1, ty))) f in
      let c', x' = generate_constraints a1 x in
      (c @ c', TApp (f', x', ty))
  | Lambda (x, t) ->
      let a1 = Union_find.make (TyVar (gensym ())) in
      let a2 = Union_find.make (TyVar (gensym ())) in
      let c, t' = generate_constraints a2 t in
      ( [
          CEq (Union_find.make (TyArrow (a1, a2)), ty);
          CLet (x, ForAll ([], [], a1), c);
        ],
        TLambda (x, a1, t', ty) )
  | Let (v, t1, t2) ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (TyVar a1) in
      let c, t1' = generate_constraints a1_ty t1 in
      let c', t2' = generate_constraints ty t2 in
      ( [ CLet (v, ForAll ([ a1 ], c, a1_ty), c') ],
        (* TODO: maybe a1 has to be in a forall *)
        TLet (v, a1_ty, t1', t2', ty) )

let rec ftv_ty (ty : ty) =
  let (`root node) = Union_find.find_set ty |> snd in
  match node.data with
  | TyVar v -> StringSet.singleton v
  | TyArrow (p, r) -> StringSet.union (ftv_ty p) (ftv_ty r)
  | TyUnit -> StringSet.empty

let rec apply_subst_ty (subst : ty Subst.t) (ty : ty) =
  (* going to need cycle detection *)
  let (`root node) = Union_find.find_set ty |> snd in
  match node.data with
  | TyVar v ->
      Subst.find_opt v subst
      |> Option.value ~default:(Union_find.make (TyVar v))
  | TyArrow (p, r) ->
      Union_find.make (TyArrow (apply_subst_ty subst p, apply_subst_ty subst r))
  | TyUnit -> Union_find.make TyUnit

let rec apply_subst_tterm subst = function
  | TVar (v, ty) -> TVar (v, apply_subst_ty subst ty)
  | TUnit ty -> TUnit (apply_subst_ty subst ty)
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
  | TLet (v, v_ty, e1, e2, ty) ->
      TLet
        ( v,
          apply_subst_ty subst v_ty,
          apply_subst_tterm subst e1,
          apply_subst_tterm subst e2,
          apply_subst_ty subst ty )

let apply_subst_subst subst on_subst = Subst.map (apply_subst_ty subst) on_subst

(* TODO: make sure correct order *)
let combose_subst subst subst' =
  Subst.union (fun _ a _ -> Some a) (apply_subst_subst subst subst') subst

let rec apply_subst_constraint subst =
 (function
 | CEq (x, y) -> CEq (apply_subst_ty subst x, apply_subst_ty subst y)
 | CInstance (var, ty) -> CInstance (var, apply_subst_ty subst ty)
 | CLet (var, forall, cos') ->
     CLet
       (var, apply_subst_scheme forall subst, apply_subst_constraints subst cos')
 | CExist (vars, cos) -> apply_subst_exist subst vars cos)

and apply_subst_constraints subst = List.map (apply_subst_constraint subst)

and apply_subst_scheme (ForAll (vars, cos, ty)) subst =
  let subst' = Subst.filter (fun name _ -> not (List.mem name vars)) subst in
  ForAll (vars, apply_subst_constraints subst' cos, apply_subst_ty subst' ty)

and apply_subst_exist subst vars cos =
  let subst' = Subst.filter (fun name _ -> not (List.mem name vars)) subst in
  CExist (vars, apply_subst_constraints subst' cos)

let apply_subst_env l subst =
  List.map (fun (name, scheme) -> (name, apply_subst_scheme scheme subst)) l
(* TODO: maybe better to substitions on the fly as opposed to with envoirnement *)

(* the way it is now we probably need to substitute into env *)
(*     b/c of clet *)

let rec unify (s : ty) (t : ty) =
  let s, `root s_data = Union_find.find_set s in
  let t, `root t_data = Union_find.find_set t in
  if s == t then ()
  else
    match (s_data.data, t_data.data) with
    | TyArrow (s1, s2), TyArrow (t1, t2) ->
        unify s1 t1;
        unify s2 t2
    | TyUnit, TyUnit -> ()
    | TyVar _, v | v, TyVar _ ->
        let _ = Union_find.union_with (fun _ _ -> v) s t in
        ()
    | _ -> ()

(* if we using cexist + union find for unification are we eventualy not going to need substition? *)
(* we might be to many env substions more that needed *)
let rec solve_constraint env cs_env : ty co -> _ = function
  | CEq (s, t) -> unify s t
  | CInstance (var, ty) ->
      (* (* TODO: better handling if not in env *) *)
      let (ForAll (vars, cos, ty')) = List.assoc var env in
      let ftv = ftv_ty ty in
      (* (* Let σ be ∀¯X[D].T. If ¯X # ftv(T′) holds, *) *)
      if List.exists (fun var -> StringSet.mem var ftv) vars then
        failwith "in ftv"
      (* we need to actualy instatinate the variables *)
        else
        (*then σ < T′ (read: T′ is an instance of σ ) *)
        (*  stands for the constraint ∃¯X.(D ∧ T ≤ T′).  *)
        let instaniate_mapping =
          (* all these would need to be added to the cs_env *)
          (* basically the ∃X *)
          List.map (fun v -> (v, Union_find.make (TyVar (gensym ())))) vars
          |> Subst.of_list
        in
        solve_constraints env cs_env
          (* by applying this "substion" we put the ∃X *)
          (* really we should do propery exist and not have to substitute *)
          (apply_subst_constraints instaniate_mapping cos
          @ [ CEq (apply_subst_ty instaniate_mapping ty', ty) ])
  | CExist (_vars, cos) ->
      (* TODO: extend the cs_env with mapping for the unification variables to union find variables*)
      solve_constraints env cs_env cos
  | CLet (var, scheme, ty) -> solve_constraints ((var, scheme) :: env) cs_env ty

and solve_constraints env cs_env = function
  | [] -> ()
  | cs :: constraints ->
      (* print_endline (constraints_to_string (cs :: constraints)); *)
      (* let subst, env' = solve_constraint env cs_env cs in *)
      solve_constraint env cs_env cs;
      (* let env' = apply_subst_env env' subst in *)
      (* let constraints' = List.map (apply_subst_constraint subst) constraints in *)
      (* print_endline (subst_to_string subst); *)
      (* if List.is_empty constraints' |> not then *)
      (* print_endline (constraints_to_string constraints'); *)
      (* let subst', env'' = solve_constraints env cs_env constraints in *)
      solve_constraints env cs_env constraints
