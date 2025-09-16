open Types
open Utils
open Ast2
open Typed_ast

(* do we need CExist: quote from tapl "Furthermore, we must bind them existentially, because we *)
(* intend the onstraint solver to choose some appropriate value for them" *)

type 't co =
  | CExist of string list * 't co list
  | CEq of 't * 't
  | CInstance of string * 't
  | CLet of
      (string * [ `for_all of string list * 't ]) list * 't co list * 't co list
  | CDef of (string * [ `ty of 't ]) list * 't co list

let rec constraint_to_string = function
  | CEq (t1, t2) -> type_to_string t1 ^ "~= " ^ type_to_string t2
  | CInstance (var, ty) -> var ^ " instanceof " ^ type_to_string ty
  | CLet (schemes, cos, cos') ->
      "let "
      ^ (List.map
           (fun (var, `for_all (vars, ty)) ->
             var ^ " :(ForAll " ^ String.concat ", " vars ^ " "
             ^ type_to_string ty ^ ") ")
           schemes
        |> String.concat ", ")
      ^ " where " ^ constraints_to_string cos ^ " in"
      ^ constraints_to_string cos'
  | CExist (vars, cos) ->
      "Exists " ^ String.concat ", " vars ^ " " ^ "."
      ^ constraints_to_string cos
  | CDef (types, cos) ->
      "def "
      ^ (List.map
           (fun (var, `ty ty) -> var ^ " : " ^ type_to_string ty ^ " ")
           types
        |> String.concat ", ")
      ^ " in " ^ constraints_to_string cos

and constraints_to_string ts =
  "[" ^ (ts |> List.map constraint_to_string |> String.concat ", ") ^ "]"

let constraints_to_string ts =
  "[\n" ^ (ts |> List.map constraint_to_string |> String.concat "\n") ^ "\n]"

type level = int

let current_level = ref 1
let enter_level () = incr current_level
let leave_level () = decr current_level
let ty_var name = TyVar { name; level = !current_level }

let rec generate_constraints_pattern ty = function
  | PVar x -> ([ (x, ty) ], [], PTVar (x, ty))
  | PWildcard -> ([], [], PTWildcard ty)
  | PUnit -> ([], [ CEq (ty, Union_find.make TyUnit) ], PTUnit ty)
  | PString b -> ([], [ CEq (ty, Union_find.make TyString) ], PTString (b, ty))
  | PBoolean b ->
      ([], [ CEq (ty, Union_find.make TyBoolean) ], PTBoolean (b, ty))
  | PFloat b -> ([], [ CEq (ty, Union_find.make TyFloat) ], PTFloat (b, ty))
  | PInteger b ->
      ([], [ CEq (ty, Union_find.make TyInteger) ], PTInteger (b, ty))
  | PConstructor { name; value } ->
      let other_variants_var = gensym () in
      let other_variants = Union_find.make (ty_var other_variants_var) in
      let value_var = gensym () in
      let value_ty = Union_find.make (ty_var value_var) in
      let env, cs, pattern' = generate_constraints_pattern value_ty value in
      let ty' =
        Union_find.make
          (TyVariant
             (Union_find.make
                (TyRowExtend
                   { label = name; field = value_ty; rest_row = other_variants })))
      in
      ( env,
        [ CExist ([ other_variants_var; value_var ], CEq (ty', ty) :: cs) ],
        PTConstructor (name, pattern', ty) )
  | PRecord row ->
      (* should this open to allow for matching on partial records? *)
      let row_init = ([], [], Union_find.make TyRowEmpty, [], []) in
      let env, cs, pattern_ty, pattern, vars =
        List.fold_right
          (fun { label; value } result ->
            let env, cs, row_ty, row, vars = result in
            let ty_name = gensym () in
            let ty = Union_find.make (ty_var ty_name) in
            let env', cs', pat' = generate_constraints_pattern ty value in

            ( env @ env',
              cs @ cs',
              Union_find.make
                (TyRowExtend { label; field = ty; rest_row = row_ty }),
              (label, pat') :: row,
              ty_name :: vars ))
          row row_init
      in
      let ty' = Union_find.make (TyRecord pattern_ty) in
      (env, [ CExist (vars, CEq (ty, ty') :: cs) ], PTRecord (pattern, ty))
  | PAscribe { pattern; ty = ty' } ->
      let env, cs, pat' = generate_constraints_pattern ty' pattern in
      (* TODO: maybe don't remove ascription from typed ast? *)
      (env, CEq (ty', ty) :: cs, pat')

let rec generate_constraints ty : _ -> ty co list * _ = function
  | Lambda { parameter; body } ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, x = generate_constraints_pattern a1_ty parameter in
      let a2 = gensym () in
      let a2_ty = Union_find.make (ty_var a2) in
      let c, t' = generate_constraints a2_ty body in
      ( [
          CExist
            ( [ a1; a2 ],
              CDef (env |> List.map (fun (v, t) -> (v, `ty t)), c)
              :: CEq
                   ( Union_find.make (TyArrow { domain = a1_ty; range = a2_ty }),
                     ty )
              :: cs );
        ],
        TLambda (x, a1_ty, t', ty) )
  | Record r ->
      let field_tys_and_constraints =
        List.map
          (fun { label; value } ->
            let var_name = gensym () in
            let ty = Union_find.make (ty_var var_name) in
            (label, ty, generate_constraints ty value, var_name))
          r
      in
      let record_ty, constraints, variables =
        List.fold_left
          (fun (rest_row, cos, vars) (label, field, (co, _), name) ->
            ( Union_find.make (TyRowExtend { label; field; rest_row }),
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
  | RecordAccess { record; projector } ->
      let rest_row_var = gensym () in
      let rest_row = Union_find.make (ty_var rest_row_var) in
      let r_var = gensym () in
      let r_ty = Union_find.make (ty_var r_var) in
      let cos, record = generate_constraints r_ty record in
      ( [
          CExist
            ( [ rest_row_var; r_var ],
              CEq
                ( ty,
                  Union_find.make
                    (TyRecord
                       (Union_find.make
                          (TyRowExtend
                             { label = projector; field = r_ty; rest_row }))) )
              :: cos );
        ],
        TRecordAccess (record, projector, ty) )
  | RecordExtend { record; new_fields } ->
      let r_var = gensym () in
      let r_ty = Union_find.make (ty_var r_var) in
      let cos, r = generate_constraints r_ty record in
      let new_field_tys_and_constraints =
        List.map
          (fun { label; value } ->
            let var_name = gensym () in
            let ty = Union_find.make (ty_var var_name) in
            (label, ty, generate_constraints ty value, var_name))
          new_fields
      in
      let new_record_ty, constraints, variables =
        List.fold_left
          (fun (rest_row, cos, vars) (label, field, (co, _), name) ->
            ( Union_find.make (TyRowExtend { label; field; rest_row }),
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
  | Integer n -> ([ CEq (ty, Union_find.make TyInteger) ], TInteger (n, ty))
  | Float n -> ([ CEq (ty, Union_find.make TyFloat) ], TFloat (n, ty))
  | String s -> ([ CEq (ty, Union_find.make TyString) ], TString (s, ty))
  | Boolean n -> ([ CEq (ty, Union_find.make TyBoolean) ], TBoolean (n, ty))
  | Var t -> ([ CInstance (t, ty) ], TVar (t, ty))
  | Application { lambda; arguement } ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, f' =
        generate_constraints
          (Union_find.make (TyArrow { domain = a1_ty; range = ty }))
          lambda
      in
      let c', x' = generate_constraints a1_ty arguement in
      ([ CExist ([ a1 ], c @ c') ], TApplication (f', x', ty))
  | Let { name; e1; e2 } ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, v = generate_constraints_pattern a1_ty name in
      let c, t1' = generate_constraints a1_ty e1 in
      leave_level ();
      let c', t2' = generate_constraints ty e2 in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              c @ cs,
              c' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TLet (v, a1_ty, t1', t2', ty) )
  | Match { value; cases } ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let cs, expr' = generate_constraints a1_ty value in
      let cs', cases' =
        List.map
          (fun { pattern; result } ->
            let env, cs, pattern' =
              generate_constraints_pattern a1_ty pattern
            in
            let cs', case' = generate_constraints ty result in

            ( CDef (env |> List.map (fun (v, t) -> (v, `ty t)), cs') :: cs,
              (pattern', case') ))
          cases
        |> List.split
      in
      let cs' = List.concat cs' in
      ([ CExist ([ a1 ], cs' @ cs) ], TMatch (expr', cases', ty))
  | Constructor { name; value } ->
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
                       (Union_find.make
                          (TyRowExtend
                             {
                               label = name;
                               field = r_ty;
                               rest_row = rest_row_ty;
                             }))) )
              :: cs );
        ],
        TConstructor (name, value', ty) )
  | LetRec { name; e1; e2 } ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, v = generate_constraints_pattern a1_ty name in
      let cs', t1' = generate_constraints a1_ty e1 in
      leave_level ();
      let cs'', t2' = generate_constraints ty e2 in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              CDef (env |> List.map (fun (v, t) -> (v, `ty t)), cs') :: cs,
              cs'' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TLet (v, a1_ty, t1', t2', ty) )
  | If { condition; consequent; alternative } ->
      let cond_var = gensym () in
      let cond_ty = Union_find.make (ty_var cond_var) in
      let cs, cond = generate_constraints cond_ty condition in
      let cs', consequent = generate_constraints ty consequent in
      let cs'', alternative = generate_constraints ty alternative in
      ( (CExist ([ cond_var ], cs) :: cs') @ cs'',
        TIf (cond, consequent, alternative, ty) )
  | Ascribe { value; ty = ty' } ->
      let cs, expr' = generate_constraints ty' value in
      (CEq (ty', ty) :: cs, expr')

let rec generate_constraints_top = function
  | [] -> ([], [])
  | Bind { name; value } :: program ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, binding = generate_constraints_pattern a1_ty name in
      let c, value = generate_constraints a1_ty value in
      leave_level ();
      let cs', program = generate_constraints_top program in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              c @ cs,
              cs' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TBind { binding; value } :: program )
  (* | Expr e :: program' -> *)
  (*     let cs, e = *)
  (*       generate_constraints (Union_find.make (ty_var (gensym ()))) e *)
  (*     in *)
  (*     let cs', program'' = generate_constraints_top program' in *)
  (*     (cs @ cs', Expr e :: program'') *)
  | RecBind { name; value } :: program ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, binding = generate_constraints_pattern a1_ty name in
      let cs', value = generate_constraints a1_ty value in
      leave_level ();
      let cs'', program = generate_constraints_top program in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              CDef (env |> List.map (fun (v, t) -> (v, `ty t)), cs') :: cs,
              cs'' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TBind { binding; value } :: program )
  | PrintString s :: program ->
      let cs, program' = generate_constraints_top program in
      (cs, TPrintString s :: program')
  | TypeBind _ :: _ -> failwith ""

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
      | ( (TyArrow { domain; range }, _),
          (TyArrow { domain = domain1; range = range1 }, _) ) ->
          inner domain domain1 ((s, t) :: used);
          inner range range1 ((s, t) :: used)
      (* could these be replaced with an structural eqaulity test *)
      | (TyUnit, _), (TyUnit, _) -> ()
      | (TyFloat, _), (TyFloat, _) -> ()
      | (TyString, _), (TyString, _) -> ()
      | (TyInteger, _), (TyInteger, _) -> ()
      | (TyBoolean, _), (TyBoolean, _) -> ()
      | (TyRowEmpty, _), (TyRowEmpty, _) -> ()
      | (TyRecord r, _), (TyRecord r', _) -> inner r r' ((s, t) :: used)
      | (TyVariant v, _), (TyVariant v', _) -> inner v v' ((s, t) :: used)
      | ( (TyRowExtend { label; field; rest_row }, _),
          ((TyRowExtend _ as ty_data), ty) ) ->
          (* | ((TyRowExtend _ as  ty_data, ty), (TyRowExtend (l, t, r), _)) -> *)
          inner_row ((s, field) :: used) label field rest_row ty ty_data
      | (TyVar _, _), (v, _) | (v, _), (TyVar _, _) ->
          Union_find.union_with (fun _ _ -> v) s t |> unit_ify (* () *)
      | _ ->
          failwith
            ("Unification Error (Symbol Clash): " ^ type_to_string s
           ^ type_to_string t)
  and inner_row used l t r ty = function
    (* ty and the arguement to function are the same *)
    (* TODO: might need cyclic checking here *)
    | TyRowExtend { label = l'; field = t'; rest_row = r' } when l = l' ->
        inner t t' used;
        inner r r' used
    | TyRowExtend { label = l'; field = t'; rest_row = r' } -> (
        let ty, `root root = Union_find.find_set r' in
        match root.data with
        | TyVar _ ->
            let beta = Union_find.make (ty_var (gensym ())) in
            let gamma = Union_find.make (ty_var (gensym ())) in
            root.data <-
              TyRowExtend { label = l; field = gamma; rest_row = beta };
            inner gamma t used;
            inner
              (Union_find.make
                 (TyRowExtend { label = l'; field = t'; rest_row = beta }))
              r used
        | _ -> inner_row used l t r ty root.data)
    | TyString | TyRowEmpty -> failwith ("Cannot add label `" ^ l ^ "` to row.")
    | TyArrow _ | TyRecord _ | TyVariant _ | TyFloat | TyInteger | TyGenVar _
    | TyVar _ | TyBoolean | TyUnit ->
        failwith
          (type_to_string ty
         ^ " is not a row, so it cannot be extended with label `" ^ l ^ "`.")
  in
  inner s t []

let generalize (`for_all (_, ty)) =
  let rec inner ty used =
    let root, `root node = Union_find.find_set ty in
    (List.assq_opt root used
    |> Option.fold
         ~some:(fun t () -> (t, StringSet.empty))
         ~none:(fun () ->
           let replacement_root = Union_find.make (ty_var (gensym ())) in
           match node.data with
           | TyVar { name; level } when level > !current_level ->
               (Union_find.make (TyGenVar name), StringSet.singleton name)
           | TyArrow { domain; range } ->
               (* dont recostruct if anything under doesn't get generalized *)
               let domain, generalized =
                 inner domain ((root, replacement_root) :: used)
               in
               let range, generalized' =
                 inner range ((root, replacement_root) :: used)
               in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyArrow { domain; range }))
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
           | TyRowExtend { label; field; rest_row } ->
               (* dont recostruct if anything under doesn't get generalized *)
               let field, generalized =
                 inner field ((root, replacement_root) :: used)
               in
               let rest_row, generalized' =
                 inner rest_row ((root, replacement_root) :: used)
               in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyRowExtend { label; field; rest_row }))
               in
               (r, StringSet.union generalized generalized')
           | TyString | TyRowEmpty | TyFloat | TyInteger | TyGenVar _ | TyUnit
           | TyVar _ | TyBoolean ->
               (ty, StringSet.empty)))
      ()
  in
  let ty, generalized_var = inner ty [] in
  `for_all (StringSet.to_list generalized_var, ty)

let instantiate (`for_all (vars, ty)) =
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
           | TyArrow { domain; range } ->
               (* dont recostruct if anything under doesn't get instantiated *)
               let domain = inner domain ((root, replacement_root) :: used) in
               let range = inner range ((root, replacement_root) :: used) in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyArrow { domain; range }))
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
           | TyRowExtend { label; field; rest_row } ->
               (* dont recostruct if anything under doesn't get generalized *)
               let field = inner field ((root, replacement_root) :: used) in
               let rest_row =
                 inner rest_row ((root, replacement_root) :: used)
               in
               let r =
                 Union_find.union replacement_root
                   (Union_find.make (TyRowExtend { label; field; rest_row }))
               in
               r
           | TyString | TyBoolean | TyRowEmpty | TyFloat | TyInteger | TyVar _
           | TyUnit ->
               ty))
      ()
  in
  inner ty []

let rec solve_constraint =
 fun env -> function
  | CEq (s, t) -> unify s t
  | CInstance (var, ty) ->
      (* TODO: better handling if not in env *)
      let ty' =
        match List.assoc var env with
        | `for_all (vars, _) as scheme ->
            let ftv = ftv_ty ty in
            (* (* Let σ be ∀¯X[D].T. If ¯X # ftv(T′) holds, *) *)
            if List.exists (fun var -> StringSet.mem var ftv) vars then
              failwith "in ftv"
            (* we need to actualy instatinate the variables *)
              else
              (*then σ < T′ (read: T′ is an instance of σ ) *)
              (*  stands for the constraint ∃¯X.(D ∧ T ≤ T′).  *)
              (* by applying this "substion" we put the ∃X *)
              instantiate scheme
        | `ty ty -> ty
      in
      solve_constraints env [ CEq (ty', ty) ]
  | CExist (_vars, cos) -> solve_constraints env cos
  | CLet (schemes, co, co') ->
      enter_level ();
      solve_constraints env co;
      leave_level ();
      solve_constraints
        (List.map (fun (var, scheme) -> (var, generalize scheme)) schemes @ env)
        co'
  | CDef (types, co) ->
      (* wish i did not have to do this coerrsion *)
      (* maybe just have one clet that either in monomorphic or polymorphic *)
      (* or just make constraint not schemes/type list not markedwith `ty or `for_all and only do that when put in env so it only happens once *)
      let types = types |> List.map (fun (v, `ty t) -> (v, `ty t)) in
      solve_constraints (types @ env) co

and solve_constraints env = function
  | [] -> ()
  | cs :: constraints ->
      solve_constraint env cs;
      solve_constraints env constraints

let infer program =
  let cos, program' = generate_constraints_top program in
  solve_constraints [] cos;
  program'
