type 'a row = (string * 'a) list

type pattern =
  | PVar of string
  | PWildcard
  | PNumber of float
  | PBoolean of bool
  | PRecord of pattern row
  (*   TODO: does record extension makes sense for patterns   *)
  | PConstructor of string * pattern

type 't tpattern =
  | PTVar of string * 't
  | PTWildcard of 't
  | PTNumber of float * 't
  | PTBoolean of bool * 't
  | PTRecord of 't tpattern row * 't
  | PTConstructor of string * 't tpattern * 't

type term =
  | Var of string
  | Lambda of string * term
  | App of term * term
  | Let of string * term * term
  | Unit
  | Number of float
  | RecordAccess of term * string
  | RecordExtend of term * term row
  | Record of term row
  | Constructor of string * term
  | Match of term * (pattern * term) list

type 't ty_f =
  | TyVar of string * int
  | TyUnit
  | TyNumber
  | TyArrow of 't * 't
  | TyRowEmpty
  | TyRowExtend of string * 't * 't
  | TyRecord of 't
  | TyVariant of 't
  | TyGenVar of string

module Subst = Map.Make (String)
module StringSet = Set.Make (String)

type 't typed_term =
  | TVar of string * 't
  | TNumber of float * 't
  | TLambda of string * 't * 't typed_term * 't
  | TApp of 't typed_term * 't typed_term * 't
  | TUnit of 't
  | TLet of string * 't * 't typed_term * 't typed_term * 't
  | TRecordAccess of 't typed_term * string * 't
  | TRecordExtend of 't typed_term * 't typed_term row * 't
  | TRecord of 't typed_term row * 't
  | TMatch of 't typed_term * ('t tpattern * 't typed_term) list * 't
  | TConstructor of string * 't typed_term * 't

type ty = 'a ty_f Union_find.elem as 'a

let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'

let type_to_string ty =
  let rec inner used ?(type_delim = ": ") ?(delim = "; ") ?(unit = "{}") ty =
    let root, `root node = Union_find.find_set ty in
    (List.assq_opt root used
    |> Option.fold
         ~some:(fun t () -> (t, [ ty ]))
         ~none:(fun () ->
           let sym = gensym () in
           match node.data with
           | TyVar (v, _) -> (v, [])
           | TyGenVar v -> (v, [])
           | TyUnit -> ("()", [])
           | TyNumber -> ("number", [])
           | TyRowEmpty -> (unit, [])
           | TyRecord t ->
               let t, used' = inner ((root, sym) :: used) ~unit:"" t in
               ("{ " ^ t ^ " }", used')
           | TyRowExtend (label, field, row_extension) ->
               let field, used' = inner ((root, sym) :: used) field in
               let row_extension, used'' =
                 inner ((root, sym) :: used) row_extension
               in
               ( label ^ type_delim ^ field ^ delim ^ row_extension,
                 used' @ used'' )
           | TyVariant row ->
               let t, used' =
                 inner ((root, sym) :: used) ~unit:"" ~delim:"| "
                   ~type_delim:" " row
               in
               ("(" ^ t ^ ")", used')
           | TyArrow (x, y) ->
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

let rec tpattern_to_string = function
  | PTVar (s, _) -> s
  | PTBoolean (b, _) -> string_of_bool b
  | PTNumber (n, _) -> string_of_float n
  | PTWildcard _ -> "_"
  | PTRecord (row, _) ->
      "{ "
      ^ (row
        |> List.map (fun (label, pat) -> label ^ " = " ^ tpattern_to_string pat)
        |> String.concat "; ")
      ^ " }"
  | PTConstructor (name, pattern, _) ->
      name ^ " (" ^ tpattern_to_string pattern ^ ")"

let tterm_to_string =
  let rec inner = function
    | TVar (v, t) -> v ^ ": " ^ type_to_string t
    | TNumber (n, _) -> string_of_float n
    | TLambda (v, v_ty, typed_term, _) ->
        "(fun (" ^ v ^ ": " ^ type_to_string v_ty ^ ") -> " ^ inner typed_term
        ^ ")"
    | TApp (f, a, _) -> "[" ^ inner f ^ " " ^ inner a ^ "]"
    | TUnit _ -> "()"
    | TRecord (row, _) ->
        "{ "
        ^ (row
          |> List.map (fun (label, value) -> label ^ " = " ^ inner value)
          |> String.concat "; ")
        ^ " }"
    | TRecordAccess (record, label, _ty) -> inner record ^ "." ^ label
    | TRecordExtend (expr, row, _) ->
        "{" ^ inner expr ^ " with "
        ^ (row
          |> List.map (fun (label, value) -> label ^ " = " ^ inner value)
          |> String.concat "; ")
        ^ "}"
    | TLet (v, v_ty, e1, e2, _) ->
        "let " ^ v ^ ": " ^ type_to_string v_ty ^ " = " ^ inner e1 ^ " in "
        ^ inner e2
    | TConstructor (name, expr, _) -> name ^ " (" ^ inner expr ^ ")"
    | TMatch (expr, cases, _) ->
        "match ( " ^ inner expr
        ^ " ) with \n"
          (* we have an indent before the first case as it does not get indented by concat *)
        ^ (cases
          |> List.map (fun (pat, case) ->
                 tpattern_to_string pat ^ " -> " ^ inner case)
          |> String.concat "\n|")
  in
  inner

(* do we need CExist: quote from tapl "Furthermore, we must bind them existentially, because we *)
(* intend the onstraint solver to choose some appropriate value for them" *)
type 't co =
  | CExist of string list * 't co list
  | CEq of 't * 't
  | CInstance of string * 't
  | CLet of string * 't scheme_co * 't co list

and 't scheme_co = ForAll of string list * 't co list * 't

(* either this of qvar i don't think we need both *)
type 't scheme = ForAll of string list * 't

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

type level = int

let current_level = ref 1
let enter_level () = incr current_level
let leave_level () = decr current_level
let ty_var var = TyVar (var, !current_level)

let rec generate_constraints ty = function
  | Record r ->
      let field_tys_and_constraints =
        List.map
          (fun (field, value) ->
            let ty = Union_find.make (ty_var (gensym ())) in
            (field, ty, generate_constraints ty value))
          r
      in
      let record_ty, constraints =
        List.fold_left
          (fun (row, cos) (field, ty, (co, _)) ->
            (Union_find.make (TyRowExtend (field, ty, row)), cos @ co))
          (Union_find.make TyRowEmpty, [])
          field_tys_and_constraints
      in
      ( CEq (ty, Union_find.make (TyRecord record_ty)) :: constraints,
        TRecord
          ( List.map
              (fun (field, _, (_, value)) -> (field, value))
              field_tys_and_constraints,
            ty ) )
  | RecordAccess (r, a) ->
      let rest_row = Union_find.make (ty_var (gensym ())) in
      let r_ty = Union_find.make (ty_var (gensym ())) in
      let cos, r = generate_constraints r_ty r in
      ( CEq
          ( ty,
            Union_find.make
              (TyRecord (Union_find.make (TyRowExtend (a, r_ty, rest_row)))) )
        :: cos,
        TRecordAccess (r, a, ty) )
  | RecordExtend (r, e) ->
      let r_ty = Union_find.make (ty_var (gensym ())) in
      let cos, r = generate_constraints r_ty r in
      let new_field_tys_and_constraints =
        List.map
          (fun (field, value) ->
            let ty = Union_find.make (ty_var (gensym ())) in
            (field, ty, generate_constraints ty value))
          e
      in
      let new_record_ty, constraints =
        List.fold_left
          (fun (row, cos) (field, ty, (co, _)) ->
            (Union_find.make (TyRowExtend (field, ty, row)), cos @ co))
          (r_ty (* TODO: might have to unrecord this type*), cos)
          new_field_tys_and_constraints
      in
      ( CEq (ty, Union_find.make (TyRecord new_record_ty)) :: constraints,
        TRecordExtend
          ( r,
            List.map
              (fun (field, _, (_, value)) -> (field, value))
              new_field_tys_and_constraints,
            ty ) )
  | Unit -> ([ CEq (ty, Union_find.make TyUnit) ], TUnit ty)
  | Number n -> ([ CEq (ty, Union_find.make TyNumber) ], TNumber (n, ty))
  | Var t -> ([ CInstance (t, ty) ], TVar (t, ty))
  | App (f, x) ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, f' =
        generate_constraints (Union_find.make (TyArrow (a1_ty, ty))) f
      in
      let c', x' = generate_constraints a1_ty x in
      ([ CExist ([ a1 ], c @ c') ], TApp (f', x', ty))
  | Lambda (x, t) ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let a2 = gensym () in
      let a2_ty = Union_find.make (ty_var a2) in
      let c, t' = generate_constraints a2_ty t in
      ( [
          CExist
            ( [ a1; a2 ],
              [
                CLet (x, ForAll ([], [], a1_ty), c);
                CEq (Union_find.make (TyArrow (a1_ty, a2_ty)), ty);
              ] );
        ],
        TLambda (x, a1_ty, t', ty) )
  | Let (v, t1, t2) ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, t1' = generate_constraints a1_ty t1 in
      leave_level ();
      let c', t2' = generate_constraints ty t2 in
      ( [ CLet (v, ForAll ([ a1 ], c, a1_ty), c') ],
        (* TODO: maybe a1 has to be in a forall *)
        TLet (v, a1_ty, t1', t2', ty) )
  | Match _ -> failwith "todo"
  | Constructor _ -> failwith "todo"

let ftv_ty (ty : ty) =
  let rec inner ty used =
    let root, `root node = Union_find.find_set ty in
    if List.memq root used then StringSet.empty
    else
      match node.data with
      | TyVar (v, _) -> StringSet.singleton v
      | TyGenVar _ -> StringSet.empty (* maybe free? *)
      | TyArrow (p, r) ->
          StringSet.union (inner p (root :: used)) (inner r (root :: used))
      | TyRecord r -> inner r (root :: used)
      | TyVariant v -> inner v (root :: used)
      | TyRowExtend (_, p, r) ->
          StringSet.union (inner p (root :: used)) (inner r (root :: used))
      | TyRowEmpty | TyUnit | TyNumber -> StringSet.empty
  in
  inner ty []

(* TODO: make sure correct order *)

(* TODO: maybe better to substitions on the fly as opposed to with envoirnement *)

(* the way it is now we probably need to substitute into env *)
(*     b/c of clet *)

let unit_ify _ = ()

let unify (s : ty) (t : ty) =
  let rec inner (s : ty) (t : ty) used =
    let s, `root s_data = Union_find.find_set s in
    let t, `root t_data = Union_find.find_set t in
    if
      List.exists
        (fun (s', t') -> (s == s' && t == t') || (t == s' && s == t'))
        used
    then ()
    else if s == t then ()
    else
      match ((s_data.data, s), (t_data.data, t)) with
      | (TyArrow (s1, s2), _), (TyArrow (t1, t2), _) ->
          inner s1 t1 ((s, t) :: used);
          inner s2 t2 ((s, t) :: used)
      | (TyUnit, _), (TyUnit, _) -> ()
      | (TyNumber, _), (TyNumber, _) -> ()
      | (TyRowEmpty, _), (TyRowEmpty, _) -> ()
      | (TyRecord r, _), (TyRecord r', _) -> inner r r' ((s, t) :: used)
      | (TyVariant v, _), (TyVariant v', _) -> inner v v' ((s, t) :: used)
      | (TyRowExtend (l, t, r), _), (ty_data, ty)
      | (ty_data, ty), (TyRowExtend (l, t, r), _) ->
          inner_row ((s, t) :: used) l t r ty ty_data
      | (TyVar _, _), (v, _) | (v, _), (TyVar _, _) ->
          Union_find.union_with (fun _ _ -> v) s t |> unit_ify (* () *)
      | _ ->
          failwith
            ("Unification Error (Symbol Clash): " ^ type_to_string s
           ^ type_to_string t)
  and inner_row used l t r ty = function
    (* ty and the arguement to function are the same *)
    (* TODO: might need cyclic checking here *)
    | TyRowExtend (l', t', r') when l = l' ->
        inner t t' used;
        inner r r' used
    | TyRowExtend (l', t', r') -> (
        let ty, `root root = Union_find.find_set r' in
        match root.data with
        | TyVar _ ->
            let beta = Union_find.make (ty_var (gensym ())) in
            let gamma = Union_find.make (ty_var (gensym ())) in
            inner gamma t used;
            inner (Union_find.make (TyRowExtend (l', t', beta))) r used;
            root.data <- TyRowExtend (l, gamma, beta)
        | _ -> inner_row used l t r ty root.data)
    | TyRowEmpty -> failwith ("Cannot add label `" ^ l ^ "` to row.")
    | TyArrow _ | TyRecord _ | TyVariant _ | TyNumber | TyGenVar _ | TyVar _
    | TyUnit ->
        failwith
          (type_to_string ty
         ^ " is not a row, so it cannot be extended with label `" ^ l ^ "`.")
  in
  inner s t []

let generalize (ForAll (_, _, ty) : 'a scheme_co) =
  let rec inner ty used =
    let root, `root node = Union_find.find_set ty in
    (List.assq_opt root used
    |> Option.fold
         ~some:(fun t () -> (t, StringSet.empty))
         ~none:(fun () ->
           let replacement_root = Union_find.make (ty_var (gensym ())) in
           match node.data with
           | TyVar (v, l) when l > !current_level ->
               (Union_find.make (TyGenVar v), StringSet.singleton v)
           | TyArrow (p, r) ->
               (* dont recostruct if anything under doesn't get generalized *)
               let p, generalized =
                 inner p ((root, replacement_root) :: used)
               in
               let r, generalized' =
                 inner r ((root, replacement_root) :: used)
               in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyArrow (p, r)))
               in
               (r, StringSet.union generalized generalized')
           | TyRecord r ->
               (* dont recostruct if anything under doesn't get generalized *)
               let r, generalized' =
                 inner r ((root, replacement_root) :: used)
               in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyRecord r))
               in
               (r, generalized')
           | TyVariant v ->
               (* dont recostruct if anything under doesn't get generalized *)
               let v, generalized =
                 inner v ((root, replacement_root) :: used)
               in
               let v =
                 Union_find.union replacement_root
                   (Union_find.make (TyVariant v))
               in
               (v, generalized)
           | TyRowExtend (l, t, r) ->
               (* dont recostruct if anything under doesn't get generalized *)
               let t, generalized =
                 inner t ((root, replacement_root) :: used)
               in
               let r, generalized' =
                 inner r ((root, replacement_root) :: used)
               in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyRowExtend (l, t, r)))
               in
               (r, StringSet.union generalized generalized')
           | TyRowEmpty | TyNumber | TyGenVar _ | TyUnit | TyVar (_, _) ->
               (ty, StringSet.empty)))
      ()
  in
  let ty, generalized_var = inner ty [] in
  ForAll (StringSet.to_list generalized_var, ty)

let instantiate (ForAll (vars, ty)) =
  let subst =
    List.map (fun v -> (v, Union_find.make (ty_var (gensym ())))) vars
    |> Subst.of_list
  in
  let rec inner ty used =
    let root, `root node = Union_find.find_set ty in
    (List.assq_opt root used
    |> Option.fold
         ~some:(fun t () -> t)
         ~none:(fun () ->
           let replacement_root = Union_find.make (ty_var (gensym ())) in
           match node.data with
           | TyGenVar v ->
               Subst.find_opt v subst
               |> Option.map (fun t -> t)
               |> Option.value ~default:ty
           | TyArrow (p, r) ->
               (* dont recostruct if anything under doesn't get instantiated *)
               let p = inner p ((root, replacement_root) :: used) in
               let r = inner r ((root, replacement_root) :: used) in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyArrow (p, r)))
               in
               r
           | TyRecord r ->
               (* dont recostruct if anything under doesn't get generalized *)
               let r = inner r ((root, replacement_root) :: used) in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyRecord r))
               in
               r
           | TyVariant v ->
               (* dont recostruct if anything under doesn't get generalized *)
               let v = inner v ((root, replacement_root) :: used) in
               let v =
                 Union_find.union replacement_root
                   (Union_find.make (TyVariant v))
               in
               v
           | TyRowExtend (l, t, r) ->
               (* dont recostruct if anything under doesn't get generalized *)
               let t = inner t ((root, replacement_root) :: used) in
               let r = inner r ((root, replacement_root) :: used) in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyRowExtend (l, t, r)))
               in
               r
           | TyRowEmpty | TyNumber | TyVar _ | TyUnit -> ty))
      ()
  in
  inner ty []

(* if we using cexist + union find for unification are we eventualy not going to need substition? *)
(* we might be to many env substions more that needed *)
let rec solve_constraint env : 'a co -> _ = function
  | CEq (s, t) -> unify s t
  | CInstance (var, ty) ->
      (* (* TODO: better handling if not in env *) *)
      let (ForAll (vars, _) as scheme) = List.assoc var env in
      let ftv = ftv_ty ty in
      (* (* Let σ be ∀¯X[D].T. If ¯X # ftv(T′) holds, *) *)
      if List.exists (fun var -> StringSet.mem var ftv) vars then
        failwith "in ftv"
      (* we need to actualy instatinate the variables *)
        else
        (*then σ < T′ (read: T′ is an instance of σ ) *)
        (*  stands for the constraint ∃¯X.(D ∧ T ≤ T′).  *)
        solve_constraints env
          (* by applying this "substion" we put the ∃X *)
          (* really we should do propery exist and not have to substitute *)
          [ CEq (instantiate scheme, ty) ]
  | CExist (_vars, cos) ->
      (* TODO: extend the cs_env with mapping for the unification variables to union find variables*)
      solve_constraints env cos
  | CLet (var, (ForAll (_, co, _ty) as scheme), co') ->
      enter_level ();
      solve_constraints env co;
      leave_level ();
      (* TODO: make new scheme type that makes it easier to generalize based on ty *)
      solve_constraints ((var, generalize scheme) :: env) co'

and solve_constraints env = function
  | [] -> ()
  | cs :: constraints ->
      solve_constraint env cs;
      solve_constraints env constraints
