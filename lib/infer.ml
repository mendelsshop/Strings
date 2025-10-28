open Types
open Utils
open Ast2
open Typed_ast

module ParsedTypeEnv = Env.Make (struct
  type t = Parsed.ty type_decl
end)

module TypeEnv = Env.Make (struct
  type t = ty type_decl
end)

module ConstructorEnv = Env.Make (struct
  (* we thunk each type constructor so that the instantiation is unique for each time we look it up *)
  type t = unit -> ty texpr
end)

module SimpleTypeEnv = Env.Make (struct
  type t = ty
end)

type env = { types : TypeEnv.t; constructors : ConstructorEnv.t }
type level = int

let current_level = ref 1
let enter_level () = incr current_level
let leave_level () = decr current_level
let ty_var name = TyVar { name; level = !current_level }

let instantiate_with_subst ty subst =
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
               Union_find.union replacement_root
                 (Union_find.make (TyArrow { domain; range }));
               replacement_root
           | TyRecord r ->
               (* dont recostruct if anything under doesn't get generalized *)
               let r = inner r ((root, replacement_root) :: used) in
               Union_find.union replacement_root (Union_find.make (TyRecord r));
               replacement_root
           | TyConstructor { ty; type_arguements } ->
               (* dont recostruct if anything under doesn't get generalized *)
               Union_find.union replacement_root
                 (Union_find.make
                    (TyConstructor
                       {
                         ty;
                         type_arguements =
                           StringMap.map
                             (fun t ->
                               inner t ((root, replacement_root) :: used))
                             type_arguements;
                       }));
               replacement_root
           | TyVariant v ->
               (* dont recostruct if anything under doesn't get generalized *)
               let v = inner v ((root, replacement_root) :: used) in
               Union_find.union replacement_root (Union_find.make (TyVariant v));
               replacement_root
           | TyRowExtend { label; field; rest_row } ->
               (* dont recostruct if anything under doesn't get generalized *)
               let field = inner field ((root, replacement_root) :: used) in
               let rest_row =
                 inner rest_row ((root, replacement_root) :: used)
               in
               Union_find.union replacement_root
                 (Union_find.make (TyRowExtend { label; field; rest_row }));
               replacement_root
           (*nominal types even though they contain other types are considered complete - inference should not change their contents *)
           | TyNominal _ | TyString | TyBoolean | TyRowEmpty | TyFloat
           | TyInteger | TyVar _ | TyUnit ->
               ty))
      ()
  in
  inner ty []

let instantiate (`for_all (vars, ty)) =
  let subst =
    List.map (fun v -> (v, Union_find.make (ty_var (gensym ())))) vars
    |> Subst.of_list
  in
  instantiate_with_subst ty subst

(* difference between this and instiatiation: *)
(* instatiation creates new types, this replaces new types *)
(* this elimnates type constructors if they lead to a type alias *)
(* this uses normal type variables as opposed to generalized type variables *)
let inline_type_alias env (ty : ty) =
  let rec inner env used (ty : ty) : ty =
    let root, `root node = Union_find.find_set ty in

    if List.memq root used then root
    else
      let union ty =
        node.data <- ty;
        root
      in
      match node.data with
      | TyVar { name; _ } ->
          SimpleTypeEnv.find_opt name env |> Option.value ~default:ty
      | TyGenVar _ | TyBoolean | TyRowEmpty | TyUnit | TyInteger | TyString
      | TyFloat | TyNominal _ ->
          ty
      | TyArrow { domain; range } ->
          let domain = inner env (root :: used) domain in
          let range = inner env (root :: used) range in
          union (TyArrow { domain; range })
      | TyRecord r ->
          let r = inner env (root :: used) r in
          union (TyRecord r)
      | TyConstructor { ty; type_arguements } -> (
          let type_arguements =
            StringMap.map (fun t -> inner env (root :: used) t) type_arguements
          in
          let _, `root node = Union_find.find_set ty in
          match node.data with
          | TyNominal _ -> union (TyConstructor { ty; type_arguements })
          | _ ->
              (* if we reach this without recursion, when the type is something like `a foo` and foo is a type alias *)
              (* if we didn't update root, because this function also is used for its effect, the type passed into this function would not get updated *)
              (* but maybe there is a better way to do this *)
              root :=
                `node
                  (inner
                     (SimpleTypeEnv.union type_arguements env)
                     (root :: used) ty);
              ty)
      | TyVariant v ->
          let v = inner env (root :: used) v in
          union (TyVariant v)
      | TyRowExtend { label; field; rest_row } ->
          let field = inner env (root :: used) field in
          let rest_row = inner env (root :: used) rest_row in
          union (TyRowExtend { label; field; rest_row })
  in
  inner env [] ty

(* converts parsed type into types for inference *)
(* the inline flag says whether to inline type constructors that are aliases, it should be only used after the type envoirnemnt (nominal and type aliases) are fully resolved *)
let to_inference_type inline (env : TypeEnv.t) inner_env =
  let rec inner' inner_env ty =
    let inner = inner' inner_env in
    let list_to_row base row =
      List.fold_right
        (fun { label; value } row ->
          Union_find.make
            (TyRowExtend { label; field = inner value; rest_row = row }))
        row
        (Option.value base ~default:(Union_find.make TyRowEmpty))
    in

    match ty with
    | Parsed.TyFloat -> Union_find.make TyFloat
    | Parsed.TyInteger -> Union_find.make TyInteger
    | Parsed.TyString -> Union_find.make TyString
    | Parsed.TyUnit -> Union_find.make TyUnit
    | Parsed.TyBoolean -> Union_find.make TyBoolean
    | Parsed.TyCon { name; arguements } ->
        if
          (* using tyvar is not good as its not generic *)
          StringSet.mem name inner_env
        then Union_find.make (TyGenVar name)
        else
          let {
            ty_variables;
            kind = NominalTypeDecl { ty; _ } | TypeDecl ty;
            _;
          } =
            TypeEnv.find name env
          in
          let ty_arguements =
            List.map
              (inner' (StringSet.union ty_variables inner_env))
              arguements
          in

          if List.length ty_arguements <> StringSet.cardinal ty_variables then
            failwith
              ("type constructor arrity mismatch for " ^ name ^ ", expected "
              ^ (ty_variables |> StringSet.cardinal |> string_of_int)
              ^ ", got "
              ^ (arguements |> List.length |> string_of_int))
          else
            let type_arguements =
              List.combine (ty_variables |> StringSet.to_list) ty_arguements
              |> StringMap.of_list
            in
            let ty = Union_find.make (TyConstructor { ty; type_arguements }) in
            if inline then inline_type_alias SimpleTypeEnv.empty ty else ty
    | Parsed.TyArrow { domain; range } ->
        Union_find.make (TyArrow { domain = inner domain; range = inner range })
    | Parsed.TyRecord { fields; extends_record } ->
        let extends_record = Option.map inner extends_record in
        Union_find.make (TyRecord (list_to_row extends_record fields))
    | Parsed.TyVariant { variants } ->
        Union_find.make (TyVariant (list_to_row None variants))
  in
  inner' inner_env

(* adds the actual type of each type declaration, and "unifies" it with the coresponding dummy type *)
(* TODO: maybe to be more "clean" (i.e. go completely with a constraint based approach) we could turn the type envoirment into constraints ... maybe thats overkill for solving the type envoirment *)
let get_type_env env
    ( _,
      { kind = NominalTypeDecl { ty = dummy_type; _ } | TypeDecl dummy_type; _ }
    ) = function
  | { name; kind = TypeDecl ty; _ } as type_decl ->
      let ty = to_inference_type false env type_decl.ty_variables ty in
      Union_find.union_with (fun x _ -> x) ty dummy_type;
      ([ (name, { type_decl with kind = TypeDecl ty }) ], [])
  | { name; kind = NominalTypeDecl { ty; id }; _ } as type_decl ->
      let get_type () =
        let ty' = to_inference_type false env type_decl.ty_variables ty in
        let ty =
          Union_find.make
            (TyNominal { name; ty = ty'; id; type_arguements = [] })
        in
        (ty, ty')
      in
      let get_constructor ty ty' =
        let sym = gensym () in
        let vars =
          type_decl.ty_variables |> StringSet.to_list
          |> List.map (fun v -> (v, Union_find.make (ty_var (gensym ()))))
          |> StringMap.of_list
        in
        let ty' = instantiate_with_subst ty' vars in

        let ty =
          Union_find.make (TyConstructor { ty; type_arguements = vars })
        in
        TLambda
          {
            span = { start = 0; finish = 0 };
            parameter =
              PTVar
                {
                  ident = sym;
                  ty = ty';
                  (* TODO: use body span once thats done *)
                  span = { start = 0; finish = 0 };
                };
            parameter_ty = ty';
            body =
              TNominalConstructor
                {
                  name;
                  value =
                    TVar
                      {
                        ident = sym;
                        ty = ty';
                        span = { start = 0; finish = 0 };
                      };
                  ty;
                  id;
                  span = { start = 0; finish = 0 };
                };
            ty = Union_find.make (TyArrow { domain = ty'; range = ty });
          }
      in
      let ty, ty' = get_type () in
      Union_find.union_with (fun x _ -> x) ty dummy_type;
      ( [ (name, { type_decl with kind = NominalTypeDecl { ty; id } }) ],
        (* for nominal types there "constructor" is also needed at the expression level *)
        (* we thunk each type constructor so that the instantiation is unique for each time we look it up *)
        [ (name, fun () -> get_constructor ty ty') ] )

let get_type_env decls =
  let inline_aliases_in_decl type_decl =
    {
      type_decl with
      kind =
        (match type_decl.kind with
        | NominalTypeDecl { ty; id; _ } -> (
            let _, `root data = Union_find.find_set ty in
            match data.data with
            | TyNominal { ty = ty'; _ } ->
                let _ = inline_type_alias SimpleTypeEnv.empty ty' in
                NominalTypeDecl { ty; id }
            | _ -> failwith "unreachable")
        | TypeDecl ty -> TypeDecl (inline_type_alias SimpleTypeEnv.empty ty));
    }
  in
  let dummy_env =
    List.map
      (fun (name, decl) ->
        ( name,
          { decl with kind = TypeDecl (Union_find.make (ty_var (gensym ()))) }
        ))
      decls
  in
  let _, decls = List.split decls in
  let envs =
    List.map2
      (get_type_env
         (dummy_env
         |> List.map (fun (name, decl) -> (name, decl))
         |> TypeEnv.of_list))
      dummy_env decls
  in
  let env, constructors =
    List.fold_right
      (fun (types, constructors) (types', constructors') ->
        (types' @ types, constructors' @ constructors))
      envs ([], [])
  in
  {
    types = env |> TypeEnv.of_list |> TypeEnv.map inline_aliases_in_decl;
    constructors = constructors |> ConstructorEnv.of_list;
  }

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

let rec generate_constraints_pattern cs_env ty = function
  (* for var see it its in nominal type env if so turn into ptnominalconstructor *)
  | PVar { ident; span } -> ([ (ident, ty) ], [], PTVar { ident; ty; span })
  | PWildcard span -> ([], [], PTWildcard { ty; span })
  | PUnit span -> ([], [ CEq (ty, Union_find.make TyUnit) ], PTUnit { ty; span })
  | PString { value; span } ->
      ([], [ CEq (ty, Union_find.make TyString) ], PTString { value; ty; span })
  | PBoolean { value; span } ->
      ( [],
        [ CEq (ty, Union_find.make TyBoolean) ],
        PTBoolean { value; ty; span } )
  | PFloat { value; span } ->
      ([], [ CEq (ty, Union_find.make TyFloat) ], PTFloat { value; ty; span })
  | PInteger { value; span } ->
      ( [],
        [ CEq (ty, Union_find.make TyInteger) ],
        PTInteger { value; ty; span } )
  | PNominalConstructor { name; value; span } -> (
      let { kind; _ } = TypeEnv.find name cs_env.types in
      match kind with
      | NominalTypeDecl { ty = ty'; _ } -> (
          let _, `root ty_data = Union_find.find_set ty' in
          match ty_data.data with
          | TyNominal { ty = ty''; id; _ } ->
              (* TODO: instantiate  *)
              let env, cs, value =
                generate_constraints_pattern cs_env ty'' value
              in
              ( env,
                CEq (ty', ty) :: cs,
                PTNominalConstructor { name; value; id; ty = ty'; span } )
          | _ -> failwith "unreachable")
      | _ -> failwith "unreachable")
  | PConstructor { name; value; span } ->
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
        PTConstructor { name; value; ty; span } )
  | PRecord { fields; span } ->
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
          fields row_init
      in
      let ty' = Union_find.make (TyRecord pattern_ty) in
      ( env,
        [ CExist (vars, CEq (ty, ty') :: cs) ],
        PTRecord { fields; ty; span } )
  | PAs { name; value; span } ->
      let env, cs, value = generate_constraints_pattern cs_env ty value in
      ((name, ty) :: env, cs, PTAs { value; name; ty; span })
  | POr { patterns = pattern :: patterns; span } ->
      let env, cs, pattern = generate_constraints_pattern cs_env ty pattern in
      let env_map = StringMap.of_list env in

      let cs, patterns =
        (* TODO: we should probably be carefull about the order of the fold as the resulting tpattern with a different ordering might change errors for duplicate pattern *)
        List.fold_left
          (fun (cs, patterns) pattern ->
            let env', cs', pattern =
              generate_constraints_pattern cs_env ty pattern
            in
            let env' = StringMap.of_list env' in
            let cs'' =
              StringMap.merge
                (fun v x y ->
                  match (x, y) with
                  (* maybe we should have some way to communicate that this is an issue with an or pattern if unification fails on one of these *)
                  | Some x, Some y -> CEq (x, y) |> Option.some
                  | Some _, None ->
                      failwith
                        ("part of or pattern " ^ tpattern_to_string pattern
                       ^ " missing variable " ^ v)
                  | None, Some _ ->
                      failwith
                        ("part of or pattern " ^ tpattern_to_string pattern
                       ^ " has extra variable " ^ v)
                  | _ -> failwith "unreachable")
                env_map env'
            in
            let cs'' = StringMap.to_list cs'' |> List.map snd in
            (* StringMap.merge *)
            (cs @ cs' @ cs'', pattern :: patterns))
          (cs, [ pattern ]) patterns
      in
      (env, cs, PTOr { patterns; ty; span })
  | POr { patterns = []; _ } -> failwith "unreachable"
  | PAscribe { pattern; ty = ty'; _ } ->
      let ty' = to_inference_type true cs_env.types StringSet.empty ty' in
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
  | Lambda { parameter; body; span } ->
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
        TLambda { parameter; parameter_ty = a1_ty; body; ty; span } )
  | Record { fields; span } ->
      let field_tys_and_constraints =
        List.map
          (fun { label; value } ->
            let var_name = gensym () in
            let ty = Union_find.make (ty_var var_name) in
            (label, ty, generate_constraints cs_state ty value, var_name))
          fields
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
            span;
          } )
  | RecordAccess { record; projector; span } ->
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
        TRecordAccess { record; projector; ty; span } )
  | RecordExtend { record; new_fields; span; _ } ->
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
            span;
            record;
            new_fields =
              List.map
                (fun (label, _, (_, value), _) -> { label; value })
                new_field_tys_and_constraints;
            ty;
          } )
  | Unit span -> ([ CEq (ty, Union_find.make TyUnit) ], TUnit { span; ty })
  | Integer { value; span; _ } ->
      ([ CEq (ty, Union_find.make TyInteger) ], TInteger { value; ty; span })
  | Float { value; span; _ } ->
      ([ CEq (ty, Union_find.make TyFloat) ], TFloat { value; ty; span })
  | String { value; span; _ } ->
      ([ CEq (ty, Union_find.make TyString) ], TString { value; ty; span })
  | Boolean { value; span; _ } ->
      ([ CEq (ty, Union_find.make TyBoolean) ], TBoolean { value; ty; span })
  | Var { ident; span; _ } ->
      ConstructorEnv.find_opt ident cs_state.constructors
      |> Option.map (fun f -> f ())
      |> Option.fold
           ~none:([ CInstance (ident, ty) ], TVar { ident; ty; span })
           ~some:(fun constructor ->
             ([ CEq (type_of_expr constructor, ty) ], constructor))
  | Application { lambda; arguement; span; _ } ->
      let a1 = gensym () in
      let a1_ty = Union_find.make (ty_var a1) in
      let c, lambda =
        generate_constraints cs_state
          (Union_find.make (TyArrow { domain = a1_ty; range = ty }))
          lambda
      in
      let c', arguement = generate_constraints cs_state a1_ty arguement in
      ([ CExist ([ a1 ], c @ c') ], TApplication { lambda; arguement; ty; span })
  | Let { name; e1; e2; span; _ } ->
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
        TLet { name; name_ty = a1_ty; e1; e2; ty; span } )
  | Match { value; cases; span; _ } ->
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
      ([ CExist ([ a1 ], cs' @ cs) ], TMatch { value; cases; ty; span })
  | Constructor { name; value; span } ->
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
        TConstructor { name; value; ty; span } )
  | LetRec { name; e1; e2; span } ->
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
        TLetRec { name; name_ty = a1_ty; e1; e2; ty; span } )
  | If { condition; consequent; alternative; span; _ } ->
      let cond_var = gensym () in
      let cond_ty = Union_find.make (ty_var cond_var) in
      let cs, condition = generate_constraints cs_state cond_ty condition in
      let cs', consequent = generate_constraints cs_state ty consequent in
      let cs'', alternative = generate_constraints cs_state ty alternative in
      ( (CExist ([ cond_var ], cs) :: cs') @ cs'',
        TIf { condition; consequent; alternative; ty; span } )
  | Ascribe { value; ty = ty''; _ } ->
      let ty' = to_inference_type true cs_state.types StringSet.empty ty'' in
      let cs, expr' = generate_constraints cs_state ty value in
      (CEq (ty', ty) :: cs, expr')

let rec generate_constraints_top cs_state = function
  | [] -> ([], [])
  | Bind { name; value; span; _ } :: program ->
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
        TBind { name; value; name_ty = a1_ty; span } :: program )
  | Expr e :: program' ->
      let cs, e =
        generate_constraints cs_state (Union_find.make (ty_var (gensym ()))) e
      in
      let cs', program'' = generate_constraints_top cs_state program' in
      (cs @ cs', TExpr e :: program'')
  | RecBind { name; value; span; _ } :: program ->
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
        TRecBind { name; value; name_ty = a1_ty; span } :: program )
  | PrintString s :: program ->
      let cs, program' = generate_constraints_top cs_state program in
      (cs, TPrintString s :: program')

(* the way it is now we probably need to substitute into env *)
(*     b/c of clet *)

let unit_ify _ = ()

let unify (s : ty) (t : ty) =
  let rec inner used (s : ty) (t : ty) =
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
          inner ((s, t) :: used) domain domain1;
          inner ((s, t) :: used) range range1
      (* could these be replaced with an structural eqaulity test *)
      | (TyUnit, _), (TyUnit, _) -> ()
      | ( (TyConstructor { type_arguements; ty }, _),
          (TyConstructor { type_arguements = type_arguements'; ty = ty' }, _) )
        ->
          let type_arguements =
            StringMap.to_list type_arguements |> List.split |> snd
          in
          let type_arguements' =
            StringMap.to_list type_arguements' |> List.split |> snd
          in
          inner used ty ty';
          List.iter2 (inner used) type_arguements type_arguements'
      | ( (TyNominal { id; name; _ }, _),
          (TyNominal { id = id'; name = name'; _ }, _) )
        when id = id' && name = name' ->
          ()
      | (TyFloat, _), (TyFloat, _) -> ()
      | (TyString, _), (TyString, _) -> ()
      | (TyInteger, _), (TyInteger, _) -> ()
      | (TyBoolean, _), (TyBoolean, _) -> ()
      | (TyRowEmpty, _), (TyRowEmpty, _) -> ()
      | (TyRecord r, _), (TyRecord r', _) -> inner ((s, t) :: used) r r'
      | (TyVariant v, _), (TyVariant v', _) -> inner ((s, t) :: used) v v'
      | ( (TyRowExtend { label; field; rest_row : ty }, _),
          ((TyRowExtend _ as ty_data), ty) ) ->
          (* | ((TyRowExtend _ as  ty_data, ty), (TyRowExtend (l, t, r), _)) -> *)
          inner used rest_row
            (inner_row ((s, field) :: used) label field ty ty_data)
      | (TyVar _, _), (v, _) | (v, _), (TyVar _, _) ->
          Union_find.union_with (fun _ _ -> v) s t
      | _ ->
          failwith
            ("Unification Error (Symbol Clash): " ^ type_to_string s ^ " =/= "
           ^ type_to_string t)
  and inner_row used l t ty : _ -> ty = function
    (* ty and the arguement to function are the same *)
    (* TODO: might need cyclic checking here *)
    | TyRowExtend { label = l'; field = t'; rest_row = r' } when l = l' ->
        inner used t t';
        r'
    | TyRowExtend { label = l'; field = t'; rest_row = r' } -> (
        let ty, `root root = Union_find.find_set r' in
        match root.data with
        | TyVar _ ->
            let beta = Union_find.make (ty_var (gensym ())) in
            let gamma = Union_find.make (ty_var (gensym ())) in
            root.data <-
              TyRowExtend { label = l; field = gamma; rest_row = beta };
            inner used gamma t;

            Union_find.make
              (TyRowExtend { label = l'; field = t'; rest_row = beta })
        | _ ->
            Union_find.make
              (TyRowExtend
                 {
                   label = l';
                   field = t';
                   rest_row = inner_row used l t ty root.data;
                 }))
    | TyRowEmpty -> failwith ("Cannot add label `" ^ l ^ "` to row.")
    (* TODO: for TyVariant and TyRecord maybe should expand past those (because if someone does { x with y = 10 }, then x will presumembly have type TyRecord and it will be the rest row of some TyRowExtend) *)
    | TyString | TyArrow _ | TyRecord _ | TyVariant _ | TyFloat | TyInteger
    | TyGenVar _ | TyVar _ | TyBoolean | TyUnit | TyNominal _
    (* if type constructor is alias mabe inline it *)
    | TyConstructor _ ->
        failwith
          (type_to_string ty
         ^ " is not a row, so it cannot be extended with label `" ^ l ^ "`.")
  in
  inner [] s t

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
               Union_find.union replacement_root
                 (Union_find.make (TyArrow { domain; range }));
               (replacement_root, StringSet.union generalized generalized')
           | TyRecord r ->
               (* dont recostruct if anything under doesn't get generalized *)
               let r, generalized' =
                 inner r ((root, replacement_root) :: used)
               in
               Union_find.union replacement_root (Union_find.make (TyRecord r));
               (replacement_root, generalized')
           | TyConstructor { ty; type_arguements } ->
               (* dont recostruct if anything under doesn't get generalized *)
               let generalized = ref StringSet.empty in
               let type_arguements =
                 StringMap.map
                   (fun t ->
                     let t, generalize =
                       inner t ((root, replacement_root) :: used)
                     in
                     generalized := StringSet.union generalize !generalized;
                     t)
                   type_arguements
               in
               Union_find.union replacement_root
                 (Union_find.make (TyConstructor { ty; type_arguements }));
               (replacement_root, !generalized)
           | TyVariant v ->
               (* dont recostruct if anything under doesn't get generalized *)
               let v, generalized =
                 inner v ((root, replacement_root) :: used)
               in
               Union_find.union replacement_root (Union_find.make (TyVariant v));
               (replacement_root, generalized)
           | TyRowExtend { label; field; rest_row } ->
               (* dont recostruct if anything under doesn't get generalized *)
               let field, generalized =
                 inner field ((root, replacement_root) :: used)
               in
               let rest_row, generalized' =
                 inner rest_row ((root, replacement_root) :: used)
               in
               Union_find.union replacement_root
                 (Union_find.make (TyRowExtend { label; field; rest_row }));

               (replacement_root, StringSet.union generalized generalized')
           | TyString | TyRowEmpty | TyFloat | TyInteger | TyGenVar _ | TyUnit
           (*nominal types even though they contain other types are considered complete - inference should not change their contents *)
           | TyNominal _ | TyVar _ | TyBoolean ->
               (ty, StringSet.empty)))
      ()
  in
  let ty, generalized_var = inner ty [] in
  `for_all (StringSet.to_list generalized_var, ty)

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
