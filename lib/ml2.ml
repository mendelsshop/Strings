type term =
  | Var of string
  | Lambda of string * term
  | App of term * term
  | Let of string * term * term

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
  | TLet of string * ty * typed_term * typed_term * ty

let rec tterm_to_string = function
  | TVar (v, ty) -> "(" ^ v ^ ": " ^ type_to_string ty ^ ")"
  | TLambda (v, v_ty, typed_term, ty) ->
      "((fun " ^ v ^ ": " ^ type_to_string v_ty ^ " -> "
      ^ tterm_to_string typed_term ^ ")" ^ ": " ^ type_to_string ty ^ ")"
  | TApp (f, a, ty) ->
      "(" ^ tterm_to_string f ^ " " ^ tterm_to_string a ^ ": "
      ^ type_to_string ty ^ ")"
  | TLet (v, v_ty, e1, e2, ty) ->
      "(let " ^ v ^ ": " ^ type_to_string v_ty ^ " = " ^ tterm_to_string e1
      ^ " in " ^ tterm_to_string e2 ^ ": " ^ type_to_string ty ^ ")"

(* do we need CExist: quote from tapl "Furthermore, we must bind them existentially, because we *)
(* intend the onstraint solver to choose some appropriate value for them" *)
type co =
  | CExist of string list * co list
  | CEq of ty * ty
  | CInstance of string * ty
  | CLet of string * scheme * co list

and scheme = ForAll of string list * co list * ty

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
  | Var t -> ([ CInstance (t, ty) ], TVar (t, ty))
  | Lambda (x, t) ->
      let a1 = gensym () in
      let a2 = gensym () in
      let c, t' = generate_constraints (TyVar a2) t in
      ( [
          CExist
            ( [ a1; a2 ],
              [
                CEq (TyArrow (TyVar a1, TyVar a2), ty);
                CLet (x, ForAll ([], [], TyVar a1), c);
              ] );
        ],
        TLambda (x, TyVar a1, t', ty) )
  | App (f, x) ->
      let a1 = gensym () in
      let c, f' = generate_constraints (TyArrow (TyVar a1, ty)) f in
      let c', x' = generate_constraints (TyVar a1) x in
      ([ CExist ([ a1 ], c @ c') ], TApp (f', x', ty))
  | Let (v, t1, t2) ->
      let a1 = gensym () in
      let c, t1' = generate_constraints (TyVar a1) t1 in
      let c', t2' = generate_constraints ty t2 in
      ( [ CLet (v, ForAll ([ a1 ], c, TyVar a1), c') ],
        (* TODO: maybe a1 has to be in a forall *)
        TLet (v, TyVar a1, t1', t2', ty) )

let rec ftv_ty = function
  | TyVar v -> StringSet.singleton v
  | TyArrow (p, r) -> StringSet.union (ftv_ty p) (ftv_ty r)
  | TyUnit -> StringSet.empty

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

(* if we using cexist + union find for unification are we eventualy not going to need substition? *)
(* we might be to many env substions more that needed *)
let rec solve_constraint env cs_env = function
  | CInstance (var, ty) ->
      (* TODO: better handling if not in env *)
      let (ForAll (vars, cos, ty')) = List.assoc var env in
      let ftv = ftv_ty ty in
      if List.exists (fun var -> StringSet.mem var ftv) vars then
        failwith "in ftv"
      (* we need to actualy instatinate the variables *)
        else
        let instaniate_mapping =
          (* all these would need to be added to the cs_env *)
          List.map (fun v -> (v, TyVar (gensym ()))) vars |> Subst.of_list
        in
        solve_constraints env cs_env
          (CEq (apply_subst_ty instaniate_mapping ty', ty) :: cos)
  | CExist (_vars, cos) ->
      (* TODO: extend the cs_env with mapping for the unification variables to union find variables*)
      solve_constraints env cs_env cos
  | CLet (var, scheme, ty) -> solve_constraints ((var, scheme) :: env) cs_env ty
  | CEq (t1, t2) when t1 = t2 -> (Subst.empty, env)
  | CEq (TyVar u, t1) | CEq (t1, TyVar u) ->
      if StringSet.mem u (type_ftv t1) then failwith "occurs check"
      else (Subst.singleton u t1, env)
  | CEq (TyArrow (tp1, tr1), TyArrow (tp2, tr2)) ->
      let subst, env' = solve_constraint env cs_env (CEq (tp1, tp2)) in
      let env' = apply_subst_env env' subst in
      let subst', env'' =
        solve_constraint env' cs_env
          (CEq (apply_subst_ty subst tr1, apply_subst_ty subst tr2))
      in
      let env'' = apply_subst_env env'' subst' in
      (combose_subst subst subst', env'')
  | _ -> failwith "error"

and solve_constraints env cs_env = function
  | [] -> (Subst.empty, env)
  | cs :: constraints ->
      print_endline (constraints_to_string (cs :: constraints));
      let subst, env' = solve_constraint env cs_env cs in
      let env' = apply_subst_env env' subst in
      let constraints' = List.map (apply_subst_constraint subst) constraints in
      print_endline (subst_to_string subst);
      if List.is_empty constraints' |> not then
        print_endline (constraints_to_string constraints');
      let subst', env'' = solve_constraints env' cs_env constraints' in
      let env'' = apply_subst_env env'' subst' in
      (combose_subst subst' subst, env'')
