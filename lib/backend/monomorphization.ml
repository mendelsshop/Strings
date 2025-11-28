open Typed_ast
open Types
open Utils

(* TODO: issues
   how to monomorphize letrecs - (polymorphic recursion issues?) - fix each let(rec) whether at the top level or not will have multiple copies of the `let pat = expr`
   something like:
   type 't let  { name: tpattern; value; 't mexpr; ty: ty; span: span }  maybe do not need span
   type 't mexpr
   | MLet { lets: 't let; e2: 't mexpr; span: span; ty: ty }
   | MLetRec { lets: 't let; e2: 't mexpr; span: span; ty: ty }
   ...
   type 't top_levl
   | MBind { lets: 't let; e2: 't mexpr;  }
   | MRecBind { lets: 't let;  }
   ...
*)

module Env = Env.Make (String)

type scheme = ty list ref
type scheme_env = scheme Env.t

(* its fine to use Env.union (whick picks the first when unioning) because everything is alpha renamed so no shadowing *)
type 't mexpr =
  | MVar of { ident : string; ty : 't; span : AMPCL.span }
  | MFloat of { value : float; ty : 't; span : AMPCL.span }
  | MString of { value : string; ty : 't; span : AMPCL.span }
  | MInteger of { value : int; ty : 't; span : AMPCL.span }
  | MBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | MLambda of {
      parameter : 't tpattern;
      parameter_ty : 't;
      body : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MMulti of { types : 't mexpr list; original : 't mexpr; ty : 't }
  | MSelect of { value : 't mexpr; selector : int; ty : 't }
  | MApplication of {
      lambda : 't mexpr;
      arguement : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MUnit of { ty : 't; span : AMPCL.span }
  (* the instantiations are for all variables bound by the let *)
  | MLet of {
      name : 't tpattern;
      name_ty : 't;
      (* if this is none than its monomorphic *)
      instances : ('t * 't) list ref option;
      e1 : 't mexpr;
      e2 : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MLetRec of {
      name : 't tpattern;
      name_ty : 't;
      instances : ('t * 't) list ref option;
      e1 : 't mexpr;
      e2 : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MIf of {
      condition : 't mexpr;
      consequent : 't mexpr;
      alternative : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MRecordAccess of {
      record : 't mexpr;
      projector : string;
      ty : 't;
      span : AMPCL.span;
    }
  | MRecordExtend of {
      record : 't mexpr;
      new_fields : 't mexpr row;
      ty : 't;
      span : AMPCL.span;
    }
  | MRecord of { fields : 't mexpr row; ty : 't; span : AMPCL.span }
  | MMatch of {
      value : 't mexpr;
      cases : ('t tpattern, 't mexpr) Ast.case list;
      ty : 't;
      span : AMPCL.span;
    }
  | MConstructor of {
      name : string;
      value : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MNominalConstructor of {
      name : string;
      value : 't mexpr;
      ty : 't;
      span : AMPCL.span;
      id : int;
    }

type 't func = {
  parameter : 't tpattern;
  parameter_ty : 't;
  free_variables : 't StringMap.t;
  body : 't mexpr;
  ty : 't;
  span : AMPCL.span;
}

type 't top_level =
  | MBind of {
      instances : ('t * 't) list ref;
      name : 't tpattern;
      name_ty : 't;
      value : 't mexpr;
      span : AMPCL.span;
    }
  | MRecBind of {
      instances : ('t * 't) list ref;
      name : 't tpattern;
      name_ty : 't;
      value : 't mexpr;
      span : AMPCL.span;
    }
  | MPrintString of string
  | MExpr of 't mexpr

let type_of_expr = function
  | MSelect { ty; _ }
  | MMulti { ty; _ }
  | MVar { ty; _ }
  | MFloat { ty; _ }
  | MString { ty; _ }
  | MInteger { ty; _ }
  | MBoolean { ty; _ }
  | MLambda { ty; _ }
  | MApplication { ty; _ }
  | MUnit { ty; _ }
  | MLet { ty; _ }
  | MLetRec { ty; _ }
  | MIf { ty; _ }
  | MRecordAccess { ty; _ }
  | MRecordExtend { ty; _ }
  | MRecord { ty; _ }
  | MMatch { ty; _ }
  | MConstructor { ty; _ }
  | MNominalConstructor { ty; _ } ->
      ty

let rec mexpr_to_string indent : ty mexpr -> string =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | MUnit _ -> "()"
  | MVar { ident; _ } -> ident
  | MSelect { selector; value; _ } ->
      mexpr_to_string indent value ^ "[" ^ string_of_int selector ^ "]"
  | MMulti { types; _ } ->
      "<"
      ^ (types |> List.map (mexpr_to_string indent) |> String.concat ",")
      ^ ">"
  | MString { value; _ } -> value
  | MInteger { value; _ } -> string_of_int value
  | MFloat { value; _ } -> string_of_float value
  | MBoolean { value; _ } -> string_of_bool value
  | MIf { condition; consequent; alternative; _ } ->
      "if ( "
      ^ mexpr_to_string indent condition
      ^ " )\n" ^ indent_string ^ "then ( "
      ^ mexpr_to_string next_level consequent
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ mexpr_to_string next_level alternative
      ^ " )"
  | MLet { name; e1; e2; _ } ->
      "let " ^ tpattern_to_string name ^ " = ( " ^ mexpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ mexpr_to_string next_level e2
      ^ " )"
  | MLetRec { name; e1; e2; _ } ->
      "let rec " ^ tpattern_to_string name ^ " = ( " ^ mexpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ mexpr_to_string next_level e2
      ^ " )"
  | MLambda { parameter; body; _ } ->
      "\\"
      ^ tpattern_to_string parameter
      ^ ".( "
      ^ mexpr_to_string indent body
      ^ " )"
  | MApplication { lambda; arguement; _ } ->
      "( "
      ^ mexpr_to_string indent lambda
      ^ " ) ( "
      ^ mexpr_to_string indent arguement
      ^ " )"
  | MRecord { fields; _ } ->
      "{\n"
      ^ (fields
        |> List.map (fun { label; value } ->
            indent_string ^ label ^ " = " ^ mexpr_to_string next_level value)
        |> String.concat ";\n")
      ^ "\n}"
  | MRecordAccess { record; projector; _ } ->
      mexpr_to_string indent record ^ "." ^ projector
  | MConstructor { name; value; _ } ->
      "`" ^ name ^ " (" ^ mexpr_to_string indent value ^ ")"
  | MNominalConstructor { name; value; _ } ->
      name ^ " (" ^ mexpr_to_string indent value ^ ")"
  | MMatch { value; cases; _ } ->
      "match ( "
      ^ mexpr_to_string indent value
      ^ " ) with \n"
      ^ indent_string
        (* we have an indent before the first case as it does not get indented by concat *)
      ^ (cases
        |> List.map (fun { Ast.pattern; result } ->
            tpattern_to_string pattern ^ " -> "
            ^ mexpr_to_string next_level result)
        |> String.concat ("\n" ^ indent_string ^ "|"))
  | MRecordExtend { record; new_fields; _ } ->
      "{"
      ^ mexpr_to_string indent record
      ^ " with "
      ^ (new_fields
        |> List.map (fun { label; value } ->
            indent_string ^ label ^ " = " ^ mexpr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"

let texpr_to_string = mexpr_to_string 0

let top_level_to_string exp =
  match exp with
  | MExpr expr -> texpr_to_string expr
  | MRecBind { name; value; _ } ->
      "let rec " ^ tpattern_to_string name ^ " = " ^ texpr_to_string value
  | MBind { name; value; _ } ->
      "let (" ^ tpattern_to_string name ^ ") = " ^ texpr_to_string value
  | MPrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)

let monomorphize_let e1 instances _env tvs =
  let ty = type_of_expr e1 in
  let substitute_instance (pat_ty, instance) =
    if pat_ty == ty then instance
    else
      failwith
        "todo: need to substitute instance into whole ty, because this \
         variable was bound by pattern"
  in
  let instances = List.map substitute_instance !instances in
  (* don't have to worry about recursive types because we are going through the type along with tye term which if finite *)
  let rec inner e _instances tvs =
    match e with
    | MLet _ | MLetRec _ -> e
    | MVar _ | MFloat _ | MString _ | MInteger _ | MBoolean _ | MUnit _ -> e
    | MLambda ({ ty; parameter_ty; body; _ } as m') as m ->
        let ftv_ty = StringSet.diff (ftv_ty parameter_ty) tvs in
        let lambda =
          MLambda
            {
              m' with
              body = inner body _instances (StringSet.union ftv_ty tvs);
            }
        in
        if StringSet.is_empty ftv_ty then lambda
        else
          MMulti
            {
              ty;
              types = (fun _ -> lambda) |> List.init (List.length _instances);
              original = m;
            }
    | MApplication ({ lambda; arguement; _ } as a) ->
        let lambda = inner lambda _instances tvs in
        let arguement = inner arguement _instances tvs in
        MApplication { a with lambda; arguement }
    | MMulti _ | MSelect _ -> e
    | MIf _ | MRecordAccess _ | MRecordExtend _ | MRecord _ | MMatch _
    | MConstructor _ | MNominalConstructor _ ->
        failwith ""
  in
  inner e1 instances tvs

let get_instantiations ty tvs pat env =
  (* all type variables bound by a specicific let should in the type of expression being let bound or else they would not be accesable *)
  let tvs' = Types.ftv_ty ty in
  let instances = if StringSet.subset tvs' tvs then None else Some (ref []) in
  let instantiations =
    Option.map
      (fun instances ->
        get_binders_with_type pat
        |> List.map (fun (name, ty) -> (name, (ty, instances)))
        |> Env.of_list)
      instances
  in
  (instances, tvs, Option.fold ~some:(Env.union env) ~none:env instantiations)

let rec monomorphize_expr env tvs = function
  | TVar { ident; ty; span } ->
      (Env.find_opt ident env
      |> Option.fold
           ~some:(fun (pat_ty, scheme) v ->
             let len = List.length !scheme in
             (* we put the pat_ty the ty of the bound variable (might not be the whole scheme i.e a in let (a, b)..., along ty the instance of that part of the scheme *)
             scheme := (pat_ty, ty) :: !scheme;
             (* what if only one instantiation or let is monomorphic *)
             MSelect { value = v; selector = len; ty })
             (* if variable not refenecinig a scheme then if its reference a variable thats type is polymorphic (bound by a scheme) than when copy the function the variable will be monoorphized *)
             (* so no need to use selector *)
           ~none:Fun.id)
        (MVar { ident; ty; span })
  (* local vars are variables captured by lambdas, and thus could be polymorphic *)
  (* | LLocalVar { ident; ty; span } -> *)
  (*     ( (Env.find_opt ident env *)
  (*       |> Option.fold *)
  (*            ~some:(fun (pat_ty, scheme) v -> *)
  (*              let len = List.length !scheme in *)
  (*              scheme := (pat_ty, ty) :: !scheme; *)
  (*              MSelect { value = v; selector = len; ty }) *)
  (*            ~none:Fun.id) *)
  (*         (MLocalVar { ident; ty; span }), *)
  (*       FunctionEnv.empty ) *)
  | TFloat { value; ty; span } -> MFloat { value; ty; span }
  | TString { value; ty; span } -> MString { value; ty; span }
  | TInteger { value; ty; span } -> MInteger { value; ty; span }
  | TBoolean { value; ty; span } -> MBoolean { value; ty; span }
  | TUnit { ty; span } -> MUnit { ty; span }
  | TLambda { body; ty; span; parameter; parameter_ty } ->
      let body = monomorphize_expr env tvs body in
      MLambda { body; ty; span; parameter_ty; parameter }
  | TApplication { lambda; arguement; ty; span } ->
      let lambda = monomorphize_expr env tvs lambda in
      let arguement = monomorphize_expr env tvs arguement in
      MApplication { lambda; arguement; ty; span }
      (* to make lets we are going to need a way to specify what the last statments should be wrapped in *)
  | TLet { name; name_ty; e1; e2; ty; span } ->
      let instances, tvs', env' =
        get_instantiations (Typed_ast.type_of_expr e1) tvs name env
      in
      let e1 = monomorphize_expr env (StringSet.union tvs' tvs) e1 in
      let e2 = monomorphize_expr env' tvs e2 in
      let e1 =
        Option.fold
          ~some:(fun instances -> monomorphize_let e1 instances env tvs)
          ~none:e1 instances
      in
      MLet { name; name_ty; e1; e2; ty; span; instances }
  | _ -> failwith ""
(* | LLetRec { name; name_ty; e1; e2; ty; span } -> *)
(*     let instances, tvs', env' = *)
(*       get_instantiations (Closure_conversion.type_of_expr e1) tvs name env *)
(*     in *)
(*     let e1 = monomorphize_expr env' (StringSet.union tvs' tvs) e1 in *)
(*     let e2 = monomorphize_expr env' tvs e2 in *)
(*     MLetRec { name; name_ty; e1; e2; ty; span; instances } *)
(* | LIf { condition; consequent; alternative; ty; span } -> *)
(*     let condition = monomorphize_expr env tvs condition in *)
(*     let consequent = monomorphize_expr env tvs consequent in *)
(*     let alternative = monomorphize_expr env tvs alternative in *)
(*     MIf { condition; consequent; alternative; ty; span } *)
(* | LRecordAccess { record; projector; ty; span } -> *)
(*     let record = monomorphize_expr env tvs record in *)
(*     MRecordAccess { record; projector; ty; span } *)
(* | LRecordExtend { record; new_fields; ty; span } -> *)
(*     let record = monomorphize_expr env tvs record in *)
(*     let new_fields = *)
(*       List.map *)
(*         (fun { label; value } -> *)
(*           let value = monomorphize_expr env tvs value in *)
(*           { value; label }) *)
(*         new_fields *)
(*     in *)
(*     MRecordExtend { record; new_fields; ty; span } *)
(* | LRecord { fields; ty; span } -> *)
(*     let fields = *)
(*       List.map *)
(*         (fun { label; value } -> *)
(*           let value = monomorphize_expr env tvs value in *)
(**)
(*           { value; label }) *)
(*         fields *)
(*     in *)
(*     MRecord { fields; ty; span } *)
(* | LMatch { value; cases; ty; span } -> *)
(*     let value = monomorphize_expr env tvs value in *)
(*     let cases = *)
(*       List.map *)
(*         (fun { Ast.pattern; result } -> *)
(*           let result = monomorphize_expr env tvs result in *)
(*           { Ast.pattern; result }) *)
(*         cases *)
(*     in *)
(*     MMatch { value; cases; ty; span } *)
(* | LConstructor { name; value; ty; span } -> *)
(*     let value = monomorphize_expr env tvs value in *)
(*     MConstructor { name; value; ty; span } *)
(* | LNominalConstructor { name; value; ty; span; id } -> *)
(*     let value = monomorphize_expr env tvs value in *)
(*     MNominalConstructor { name; value; ty; span; id } *)

let monomorphize_tl env = function
  | TBind { name; name_ty; value; span } ->
      let instances = ref [] in
      let instantiations =
        get_binders_with_type name
        |> List.map (fun (name, ty) -> (name, (ty, instances)))
        |> Env.of_list
      in

      let tvs = Types.ftv_ty (Typed_ast.type_of_expr value) in
      let value = monomorphize_expr env tvs value in

      let env = Env.union instantiations env in
      (env, MBind { name; name_ty; value; span; instances })
  | TRecBind { name; name_ty; value; span } ->
      let instances = ref [] in
      let tvs = Types.ftv_ty (Typed_ast.type_of_expr value) in
      let instantiations =
        get_binders_with_type name
        |> List.map (fun (name, ty) -> (name, (ty, instances)))
        |> Env.of_list
      in
      let env = Env.union instantiations env in

      let value = monomorphize_expr env tvs value in
      (env, MRecBind { name; name_ty; value; span; instances })
  | TExpr expr ->
      let expr = monomorphize_expr env StringSet.empty expr in
      (env, MExpr expr)
  | TPrintString s -> (env, MPrintString s)

let monomorphize_tls ?(env = Env.empty) tls =
  List.fold_left_map monomorphize_tl env tls |> snd
(* once we gather up each let/bind instances we can think modify the let *)
