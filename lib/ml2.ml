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
          CEq (TyArrow (TyVar a1, TyVar a2), ty);
          CLet (x, ForAll ([], [], TyVar a1), c);
        ],
        TLambda (x, TyVar a1, t', ty) )
  | App (f, x) ->
      let a1 = gensym () in
      let c, f' = generate_constraints (TyArrow (TyVar a1, ty)) f in
      let c', x' = generate_constraints (TyVar a1) x in
      (c @ c', TApp (f', x', ty))
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
 | CLet (var, ForAll (vars, cos, ty), cos') ->
     let subst' = Subst.filter (fun name _ -> List.mem name vars) subst in
     CLet
       ( var,
         ForAll
           (vars, apply_subst_constraints subst' cos, apply_subst_ty subst' ty),
         apply_subst_constraints subst cos' ))

and apply_subst_constraints subst = List.map (apply_subst_constraint subst)

(* TODO: maybe better to substitions on the fly as opposed to with envoirnement *)
let rec solve_constraint env = function
  | CInstance (var, ty) ->
      (* TODO: better handling if not in env *)
      let (ForAll (vars, cos, ty')) = List.assoc var env in
      let ftv = ftv_ty ty in
      if List.exists (fun var -> StringSet.mem var ftv) vars then
        failwith "in ftv"
      else solve_constraints env (CEq (ty, ty') :: cos)
  | CLet (var, scheme, ty) -> solve_constraints ((var, scheme) :: env) ty
  | CEq (t1, t2) when t1 = t2 -> Subst.empty
  | CEq (TyVar u, t1) | CEq (t1, TyVar u) ->
      if StringSet.mem u (type_ftv t1) then failwith "occurs check"
      else Subst.singleton u t1
  | CEq (TyArrow (tp1, tr1), TyArrow (tp2, tr2)) ->
      let subst = solve_constraint env (CEq (tp1, tp2)) in
      let subst' =
        solve_constraint env
          (CEq (apply_subst_ty subst tr1, apply_subst_ty subst tr2))
      in
      combose_subst subst subst'
  | _ -> failwith "error"

and solve_constraints env = function
  | [] -> Subst.empty
  | cs :: constraints ->
      let subst = solve_constraint env cs in
      let constraints' = List.map (apply_subst_constraint subst) constraints in
      let subst' = solve_constraints env constraints' in
      combose_subst subst' subst
