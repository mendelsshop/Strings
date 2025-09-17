open Types
open Utils
open Ast2
open Typed_ast

module TypeEnv = Env.Make (struct
  type t = ty
end)

module ConstructorEnv = Env.Make (struct
  type t = ty texpr
end)

type env = { types : TypeEnv.t; constructors : ConstructorEnv.t }

(* do we need CExist: quote from tapl "Furthermore, we must bind them existentially, because we *)
(* intend the onstraint solver to choose some appropriate value for them" *)
let get_type_env = function
  | Ast.Bind _ | RecBind _ | PrintString _ -> ([], [])
  | TypeBind { name; ty } ->
      ([ (name, ty) ], [])
      (* for nominal types there "constructor" is also needed at the expression level *)
  | NominalTypeBind { name; ty } -> (
      let _, `root ty_data = Union_find.find_set ty in
      let sym = gensym () in
      match ty_data.data with
      | TyNominal { ty = ty'; id; _ } ->
          ( [ (name, ty) ],
            [
              ( name,
                TLambda
                  {
                    parameter = PTVar { ident = sym; ty = ty' };
                    parameter_ty = ty';
                    body =
                      TNominalConstructor
                        { name; value = TVar { ident = sym; ty = ty' }; ty; id };
                    ty = Union_find.make (TyArrow { domain = ty'; range = ty });
                  } );
            ] )
      | _ -> failwith "unreachable")

let get_type_env program =
  let envs = List.map get_type_env program in
  List.fold_right
    (fun (types, constructors) (types', constructors') ->
      (types' @ types, constructors' @ constructors))
    envs ([], [])

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

let rec generate_constraints_pattern cs_env ty = function
  (* for var see it its in nominal type env if so turn into ptnominalconstructor *)
  | PVar ident -> ([ (ident, ty) ], [], PTVar { ident; ty })
  | PWildcard -> ([], [], PTWildcard ty)
  | PUnit -> ([], [ CEq (ty, Union_find.make TyUnit) ], PTUnit ty)
  | PString value ->
      ([], [ CEq (ty, Union_find.make TyString) ], PTString { value; ty })
  | PBoolean value ->
      ([], [ CEq (ty, Union_find.make TyBoolean) ], PTBoolean { value; ty })
  | PFloat value ->
      ([], [ CEq (ty, Union_find.make TyFloat) ], PTFloat { value; ty })
  | PInteger value ->
      ([], [ CEq (ty, Union_find.make TyInteger) ], PTInteger { value; ty })
  | PNominalConstructor { name; value } -> (
      let ty' = TypeEnv.find name cs_env.types in
      let _, `root ty_data = Union_find.find_set ty' in
      match ty_data.data with
      | TyNominal { ty = ty''; id; _ } ->
          let env, cs, value = generate_constraints_pattern cs_env ty'' value in
          ( env,
            CEq (ty', ty) :: cs,
            PTNominalConstructor { name; value; id; ty = ty' } )
      | _ -> failwith "unreachable")
  | PConstructor { name; value } ->
      let other_variants_var = gensym () in
      let other_variants = Union_find.make (ty_var other_variants_var) in
      let value_var = gensym () in
      let value_ty = Union_find.make (ty_var value_var) in
      let env, cs, value = generate_constraints_pattern cs_env value_ty value in
      let ty' =
        Union_find.make
          (TyVariant
             (Union_find.make
                (TyRowExtend
                   { label = name; field = value_ty; rest_row = other_variants })))
      in
      ( env,
        [ CExist ([ other_variants_var; value_var ], CEq (ty', ty) :: cs) ],
        PTConstructor { name; value; ty } )
  | PRecord row ->
      (* should this open to allow for matching on partial records? *)
      let row_init = ([], [], Union_find.make TyRowEmpty, [], []) in
      let env, cs, pattern_ty, fields, vars =
        List.fold_right
          (fun { label; value } result ->
            let env, cs, row_ty, row, vars = result in
            let ty_name = gensym () in
            let ty = Union_find.make (ty_var ty_name) in
            let env', cs', value =
              generate_constraints_pattern cs_env ty value
            in

            ( env @ env',
              cs @ cs',
              Union_find.make
                (TyRowExtend { label; field = ty; rest_row = row_ty }),
              { label; value } :: row,
              ty_name :: vars ))
          row row_init
      in
      let ty' = Union_find.make (TyRecord pattern_ty) in
      (env, [ CExist (vars, CEq (ty, ty') :: cs) ], PTRecord { fields; ty })
  | PAscribe { pattern; ty = ty' } ->
      let env, cs, pat' = generate_constraints_pattern cs_env ty' pattern in
      (* TODO: maybe don't remove ascription from typed ast? *)
      (env, CEq (ty', ty) :: cs, pat')

(* new binders should remove variables being binded from constructor list of cs_state this is how we shaddow constructors *)
let shaddow { types; constructors } binders =
  {
    types;
    constructors =
      ConstructorEnv.merge
        (fun _ x y -> if Option.is_some y then None else x)
        constructors
        (ConstructorEnv.of_list binders);
  }

let rec generate_constraints cs_state ty : _ -> ty co list * _ = function
  | Lambda { parameter; body } ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, parameter =
        generate_constraints_pattern cs_state a1_ty parameter
      in
      let a2 = gensym () in
      let a2_ty = Union_find.make (ty_var a2) in
      let c, body = generate_constraints (shaddow cs_state env) a2_ty body in
      ( [
          CExist
            ( [ a1; a2 ],
              CDef (env |> List.map (fun (v, t) -> (v, `ty t)), c)
              :: CEq
                   ( Union_find.make (TyArrow { domain = a1_ty; range = a2_ty }),
                     ty )
              :: cs );
        ],
        TLambda { parameter; parameter_ty = a1_ty; body; ty } )
  | Record r ->
      let field_tys_and_constraints =
        List.map
          (fun { label; value } ->
            let var_name = gensym () in
            let ty = Union_find.make (ty_var var_name) in
            (label, ty, generate_constraints cs_state ty value, var_name))
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
          {
            fields =
              List.map
                (fun (label, _, (_, value), _) -> { label; value })
                field_tys_and_constraints;
            ty;
          } )
  | RecordAccess { record; projector } ->
      let rest_row_var = gensym () in
      let rest_row = Union_find.make (ty_var rest_row_var) in
      let r_var = gensym () in
      let r_ty = Union_find.make (ty_var r_var) in
      let cos, record = generate_constraints cs_state r_ty record in
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
        TRecordAccess { record; projector; ty } )
  | RecordExtend { record; new_fields } ->
      let r_var = gensym () in
      let r_ty = Union_find.make (ty_var r_var) in
      let cos, record = generate_constraints cs_state r_ty record in
      let new_field_tys_and_constraints =
        List.map
          (fun { label; value } ->
            let var_name = gensym () in
            let ty = Union_find.make (ty_var var_name) in
            (label, ty, generate_constraints cs_state ty value, var_name))
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
          {
            record;
            new_fields =
              List.map
                (fun (label, _, (_, value), _) -> { label; value })
                new_field_tys_and_constraints;
            ty;
          } )
  | Unit -> ([ CEq (ty, Union_find.make TyUnit) ], TUnit ty)
  | Integer value ->
      ([ CEq (ty, Union_find.make TyInteger) ], TInteger { value; ty })
  | Float value -> ([ CEq (ty, Union_find.make TyFloat) ], TFloat { value; ty })
  | String value ->
      ([ CEq (ty, Union_find.make TyString) ], TString { value; ty })
  | Boolean value ->
      ([ CEq (ty, Union_find.make TyBoolean) ], TBoolean { value; ty })
  | Var ident ->
      ConstructorEnv.find_opt ident cs_state.constructors
      |> Option.fold
           ~none:([ CInstance (ident, ty) ], TVar { ident; ty })
           ~some:(fun constructor ->
             ([ CEq (type_of_expr constructor, ty) ], constructor))
  | Application { lambda; arguement } ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, lambda =
        generate_constraints cs_state
          (Union_find.make (TyArrow { domain = a1_ty; range = ty }))
          lambda
      in
      let c', arguement = generate_constraints cs_state a1_ty arguement in
      ([ CExist ([ a1 ], c @ c') ], TApplication { lambda; arguement; ty })
  | Let { name; e1; e2 } ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, name = generate_constraints_pattern cs_state a1_ty name in
      let c, e1 = generate_constraints cs_state a1_ty e1 in
      leave_level ();
      let c', e2 = generate_constraints (shaddow cs_state env) ty e2 in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              c @ cs,
              c' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TLet { name; name_ty = a1_ty; e1; e2; ty } )
  | Match { value; cases } ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let cs, value = generate_constraints cs_state a1_ty value in
      let cs', cases =
        List.map
          (fun { pattern; result } ->
            let env, cs, pattern =
              generate_constraints_pattern cs_state a1_ty pattern
            in
            let cs', result =
              generate_constraints (shaddow cs_state env) ty result
            in

            ( CDef (env |> List.map (fun (v, t) -> (v, `ty t)), cs') :: cs,
              { pattern; result } ))
          cases
        |> List.split
      in
      let cs' = List.concat cs' in
      ([ CExist ([ a1 ], cs' @ cs) ], TMatch { value; cases; ty })
  | Constructor { name; value } ->
      let r = gensym () in
      let r_ty = Union_find.make (ty_var r) in
      let cs, value = generate_constraints cs_state r_ty value in
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
        TConstructor { name; value; ty } )
  | LetRec { name; e1; e2 } ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, name = generate_constraints_pattern cs_state a1_ty name in
      let cs', e1 = generate_constraints (shaddow cs_state env) a1_ty e1 in
      leave_level ();
      let cs'', e2 = generate_constraints (shaddow cs_state env) ty e2 in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              CDef (env |> List.map (fun (v, t) -> (v, `ty t)), cs') :: cs,
              cs'' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TLetRec { name; name_ty = a1_ty; e1; e2; ty } )
  | If { condition; consequent; alternative } ->
      let cond_var = gensym () in
      let cond_ty = Union_find.make (ty_var cond_var) in
      let cs, condition = generate_constraints cs_state cond_ty condition in
      let cs', consequent = generate_constraints cs_state ty consequent in
      let cs'', alternative = generate_constraints cs_state ty alternative in
      ( (CExist ([ cond_var ], cs) :: cs') @ cs'',
        TIf { condition; consequent; alternative; ty } )
  | Ascribe { value; ty = ty' } ->
      let cs, expr' = generate_constraints cs_state ty' value in
      (CEq (ty', ty) :: cs, expr')

let rec generate_constraints_top cs_state = function
  | [] -> ([], [])
  | Bind { name; value } :: program ->
      enter_level ();
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let env, cs, name = generate_constraints_pattern cs_state a1_ty name in
      let c, value = generate_constraints cs_state a1_ty value in
      leave_level ();
      let cs', program =
        generate_constraints_top (shaddow cs_state env) program
      in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              c @ cs,
              cs' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TBind { name; value } :: program )
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
      let env, cs, name = generate_constraints_pattern cs_state a1_ty name in
      let cs', value =
        generate_constraints (shaddow cs_state env) a1_ty value
      in
      leave_level ();
      let cs'', program =
        generate_constraints_top (shaddow cs_state env) program
      in
      ( [
          CLet
            ( List.map (fun (name, ty) -> (name, `for_all ([ a1 ], ty))) env,
              CDef (env |> List.map (fun (v, t) -> (v, `ty t)), cs') :: cs,
              cs'' );
        ],
        (* TODO: maybe a1 has to be in a forall *)
        TRecBind { name; value } :: program )
  | PrintString s :: program ->
      let cs, program' = generate_constraints_top cs_state program in
      (cs, TPrintString s :: program')

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
      | ( (TyNominal { id; name; _ }, _),
          (TyNominal { id = id'; name = name'; _ }, _) )
        when id = id' && name = name' ->
          ()
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
            ("Unification Error (Symbol Clash): " ^ type_to_string s ^ " =/= "
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
    | TyVar _ | TyBoolean | TyUnit | TyNominal _ ->
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
           (*nominal types even though they contain other types are considered complete - inference should not change their contents *)
           | TyNominal _ | TyVar _ | TyBoolean ->
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
           (*nominal types even though they contain other types are considered complete - inference should not change their contents *)
           | TyNominal _ | TyUnit ->
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

let infer program env =
  let cos, program' = generate_constraints_top env program in
  solve_constraints [] cos;
  program'
