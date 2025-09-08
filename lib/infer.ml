open Types
open Utils
open Expr

(* do we need CExist: quote from tapl "Furthermore, we must bind them existentially, because we *)
(* intend the onstraint solver to choose some appropriate value for them" *)
type 't co =
  | CExist of string list * 't co list
  | CEq of 't * 't
  | CInstance of string * 't
  | CLet of (string * 't scheme) list * 't co list * 't co list

(* either this of qvar i don't think we need both *)
and 't scheme = ForAll of string list * 't

let rec constraint_to_string = function
  | CEq (t1, t2) -> type_to_string t1 ^ "~= " ^ type_to_string t2
  | CInstance (var, ty) -> var ^ " instanceof " ^ type_to_string ty
  | CLet (schemes, cos, cos') ->
      "let "
      ^ (List.map
           (fun (var, ForAll (vars, ty)) ->
             var ^ " :(ForAll " ^ String.concat ", " vars ^ " "
             ^ type_to_string ty ^ ") ")
           schemes
        |> String.concat ", ")
      ^ " where " ^ constraints_to_string cos ^ " in"
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

let rec generate_constraints_pattern ty = function
  | PVar x -> ([ (x, ty) ], [], PTVar (x, ty))
  | PWildcard -> ([], [], PTWildcard ty)
  | PBoolean b ->
      ([], [ CEq (ty, Union_find.make TyBoolean) ], PTBoolean (b, ty))
  | PNumber b -> ([], [ CEq (ty, Union_find.make TyNumber) ], PTNumber (b, ty))
  | PConstructor (name, pattern) ->
      let other_variants = Union_find.make (ty_var (gensym ())) in
      let value_ty = Union_find.make (ty_var (gensym ())) in
      let env, cs, pattern' = generate_constraints_pattern value_ty pattern in
      let ty' =
        Union_find.make
          (TyVariant
             (Union_find.make (TyRowExtend (name, value_ty, other_variants))))
      in
      (env, CEq (ty', ty) :: cs, PTConstructor (name, pattern', ty))
  | PRecord row ->
      (* should this open to allow for matching on partial records? *)
      let row_init = ([], [], Union_find.make TyRowEmpty, []) in
      let env, cs, pattern_ty, pattern =
        List.fold_right
          (fun (label, pattern) result ->
            let env, cs, row_ty, row = result in
            let ty = Union_find.make (ty_var (gensym ())) in
            let env', cs', pat' = generate_constraints_pattern ty pattern in

            ( env @ env',
              cs @ cs',
              Union_find.make (TyRowExtend (label, ty, row_ty)),
              (label, pat') :: row ))
          row row_init
      in
      let ty' = Union_find.make (TyRecord pattern_ty) in
      (env, CEq (ty, ty') :: cs, PTRecord (pattern, ty))

let rec generate_constraints ty = function
  | Record r ->
      let field_tys_and_constraints =
        List.map
          (fun (field, value) ->
            let var_name = gensym () in
            let ty = Union_find.make (ty_var var_name) in
            (field, ty, generate_constraints ty value, var_name))
          r
      in
      let record_ty, constraints, variables =
        List.fold_left
          (fun (row, cos, vars) (field, ty, (co, _), name) ->
            ( Union_find.make (TyRowExtend (field, ty, row)),
              cos @ co,
              name :: vars ))
          (Union_find.make TyRowEmpty, [], [])
          field_tys_and_constraints
      in
      ( [
          CExist
            ( variables,
              CEq (ty, Union_find.make (TyRecord record_ty)) :: constraints );
        ],
        TRecord
          ( List.map
              (fun (field, _, (_, value), _) -> (field, value))
              field_tys_and_constraints,
            ty ) )
  | RecordAccess (r, a) ->
      let rest_row_var = gensym () in
      let rest_row = Union_find.make (ty_var rest_row_var) in
      let r_var = gensym () in
      let r_ty = Union_find.make (ty_var r_var) in
      let cos, r = generate_constraints r_ty r in
      ( [
          CExist
            ( [ rest_row_var; r_var ],
              CEq
                ( ty,
                  Union_find.make
                    (TyRecord
                       (Union_find.make (TyRowExtend (a, r_ty, rest_row)))) )
              :: cos );
        ],
        TRecordAccess (r, a, ty) )
  | RecordExtend (r, e) ->
      let r_var = gensym () in
      let r_ty = Union_find.make (ty_var r_var) in
      let cos, r = generate_constraints r_ty r in
      let new_field_tys_and_constraints =
        List.map
          (fun (field, value) ->
            let var_name = gensym () in
            let ty = Union_find.make (ty_var var_name) in
            (field, ty, generate_constraints ty value, var_name))
          e
      in
      let new_record_ty, constraints, variables =
        List.fold_left
          (fun (row, cos, vars) (field, ty, (co, _), name) ->
            ( Union_find.make (TyRowExtend (field, ty, row)),
              cos @ co,
              name :: vars ))
          (r_ty (* TODO: might have to unrecord this type*), cos, [ r_var ])
          new_field_tys_and_constraints
      in
      ( [
          CExist
            ( variables,
              CEq (ty, Union_find.make (TyRecord new_record_ty)) :: constraints
            );
        ],
        TRecordExtend
          ( r,
            List.map
              (fun (field, _, (_, value), _) -> (field, value))
              new_field_tys_and_constraints,
            ty ) )
  | Unit -> ([ CEq (ty, Union_find.make TyUnit) ], TUnit ty)
  | Number n -> ([ CEq (ty, Union_find.make TyNumber) ], TNumber (n, ty))
  | Boolean n -> ([ CEq (ty, Union_find.make TyBoolean) ], TBoolean (n, ty))
  | Var t -> ([ CInstance (t, ty) ], TVar (t, ty))
  | Application (f, x) ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, f' =
        generate_constraints (Union_find.make (TyArrow (a1_ty, ty))) f
      in
      let c', x' = generate_constraints a1_ty x in
      ([ CExist ([ a1 ], c @ c') ], TApplication (f', x', ty))
  | Lambda (x, t) ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, x = generate_constraints_pattern a1_ty x in
      let a2 = gensym () in
      let a2_ty = Union_find.make (ty_var a2) in
      let c, t' = generate_constraints a2_ty t in
      ( [
          CExist
            ( [ a1; a2 ],
              CLet
                (List.map (fun (name, ty) -> (name, ForAll ([], ty))) env, [], c)
              :: CEq (Union_find.make (TyArrow (a1_ty, a2_ty)), ty)
              :: cs );
        ],
        TLambda (x, a1_ty, t', ty) )
  | Let (PVar v, t1, t2) ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, t1' = generate_constraints a1_ty t1 in
      leave_level ();
      let c', t2' = generate_constraints ty t2 in
      ( [ CLet ([ (v, ForAll ([ a1 ], a1_ty)) ], c, c') ],
        (* TODO: maybe a1 has to be in a forall *)
        TLet (PTVar (v, a1_ty), a1_ty, t1', t2', ty) )
  | Match _ -> failwith "todo match"
  | Constructor (name, value) ->
      let r = gensym () in
      let r_ty = Union_find.make (ty_var r) in
      let cs, value' = generate_constraints r_ty value in
      let rest_row = gensym () in
      let rest_row_ty = Union_find.make (ty_var rest_row) in
      ( [
          CExist
            ( [ r; rest_row ],
              CEq
                ( ty,
                  Union_find.make
                    (TyVariant
                       (Union_find.make (TyRowExtend (name, r_ty, rest_row_ty))))
                )
              :: cs );
        ],
        TConstructor (name, value', ty) )
  | LetRec _ -> failwith "todo letrec"
  | If (cond, consequent, alternative) ->
      let cond_var = gensym () in
      let cond_ty = Union_find.make (ty_var cond_var) in
      let cs, cond = generate_constraints cond_ty cond in
      let cs', consequent = generate_constraints ty consequent in
      let cs'', alternative = generate_constraints ty alternative in
      ( (CExist ([ cond_var ], cs) :: cs') @ cs'',
        TIf (cond, consequent, alternative, ty) )
  | _ -> failwith "todo let with pattern"

let rec generate_constraints_top = function
  | [] -> ([], [])
  | Bind (PVar v, e) :: cs ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, t1' = generate_constraints a1_ty e in
      leave_level ();
      let cs, program = generate_constraints_top cs in
      ( [ CLet ([ (v, ForAll ([ a1 ], a1_ty)) ], c, cs) ],
        (* TODO: maybe a1 has to be in a forall *)
        Bind (PTVar (v, a1_ty), t1') :: program )
  | Expr e :: program' ->
      let cs, e =
        generate_constraints (Union_find.make (ty_var (gensym ()))) e
      in
      let cs', program'' = generate_constraints_top program' in
      (cs @ cs', Expr e :: program'')
  | Bind _ :: _ -> failwith "todo tl let with pattern"
  | RecBind (_, _) :: _ -> failwith "todo tl letrec"
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
      | (TyBoolean, _), (TyBoolean, _) -> ()
      | (TyRowEmpty, _), (TyRowEmpty, _) -> ()
      | (TyRecord r, _), (TyRecord r', _) -> inner r r' ((s, t) :: used)
      | (TyVariant v, _), (TyVariant v', _) -> inner v v' ((s, t) :: used)
      | (TyRowExtend (l, t, r), _), ((TyRowExtend _ as ty_data), ty) ->
          (* | ((TyRowExtend _ as  ty_data, ty), (TyRowExtend (l, t, r), _)) -> *)
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
            root.data <- TyRowExtend (l, gamma, beta);
            inner gamma t used;
            inner (Union_find.make (TyRowExtend (l', t', beta))) r used
        | _ -> inner_row used l t r ty root.data)
    | TyRowEmpty -> failwith ("Cannot add label `" ^ l ^ "` to row.")
    | TyArrow _ | TyRecord _ | TyVariant _ | TyNumber | TyGenVar _ | TyVar _
    | TyBoolean | TyUnit ->
        failwith
          (type_to_string ty
         ^ " is not a row, so it cannot be extended with label `" ^ l ^ "`.")
  in
  inner s t []

let generalize (ForAll (_, ty) : 'a scheme) =
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
           | TyRowEmpty | TyNumber | TyGenVar _ | TyUnit
           | TyVar (_, _)
           | TyBoolean ->
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
           | TyBoolean | TyRowEmpty | TyNumber | TyVar _ | TyUnit -> ty))
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
  | CLet (schemes, co, co') ->
      enter_level ();
      solve_constraints env co;
      leave_level ();
      (* TODO: make new scheme type that makes it easier to generalize based on ty *)
      solve_constraints
        (List.map (fun (var, scheme) -> (var, generalize scheme)) schemes @ env)
        co'

and solve_constraints env = function
  | [] -> ()
  | cs :: constraints ->
      solve_constraint env cs;
      solve_constraints env constraints

let infer program =
  (* TODO: env *)
  let cos, program' = generate_constraints_top program in
  print_endline (constraints_to_string cos);
  solve_constraints [] cos;
  print_endline (constraints_to_string cos);
  program'
