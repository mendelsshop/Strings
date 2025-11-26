open Closure_conversion
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
  | MLocalVar of { ident : string; ty : 't; span : AMPCL.span }
  | MFloat of { value : float; ty : 't; span : AMPCL.span }
  | MString of { value : string; ty : 't; span : AMPCL.span }
  | MInteger of { value : int; ty : 't; span : AMPCL.span }
  | MBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | MLambda of { name : int; ty : 't; span : AMPCL.span }
  | MMulti of { types : scheme; value : 't mexpr }
  | MSelect of { value : 't mexpr; selector : int }
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
      e1 : 't mexpr;
      e2 : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MLetRec of {
      name : 't tpattern;
      name_ty : 't;
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

type 't mfunc = 't func list

module FunctionEnv = Utils.Env.Make (Int)

type 't functions = ty func Env.t

type 't top_level =
  | MBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't mexpr;
      span : AMPCL.span;
    }
  | MRecBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't mexpr;
      span : AMPCL.span;
    }
  | MPrintString of string
  | MExpr of 't mexpr

let rec mexpr_to_string indent : ty mexpr -> string =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | MUnit _ -> "()"
  | MVar { ident; _ } -> ident
  | MLocalVar { ident; _ } -> ident
  | MSelect { selector; value } ->
      mexpr_to_string indent value ^ "[" ^ string_of_int selector ^ "]"
  | MMulti _ -> "multi"
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
  | MLambda _ -> "lambda"
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

let rec monomorphize_expr env = function
  | LVar { ident; ty; span } ->
      (Env.find_opt ident env
      |> Option.fold
           ~some:(fun (ty, scheme) v ->
             let len = List.length !scheme in
             scheme := ty :: !scheme;
             (* what if only one instantiation or let is monomorphic *)
             MSelect { value = v; selector = len })
             (* if variable not refenecinig a scheme then if its reference a variable thats type is polymorphic (bound by a scheme) than when copy the function the variable will be monoorphized *)
             (* so no need to use selector *)
           ~none:Fun.id)
        (MVar { ident; ty; span })
  (* local vars are variables captured by lambdas, and thus could be polymorphic *)
  | LLocalVar { ident; ty; span } ->
      (Env.find_opt ident env
      |> Option.fold
           ~some:(fun (ty, scheme) v ->
             let len = List.length !scheme in
             scheme := ty :: !scheme;
             MSelect { value = v; selector = len })
           ~none:Fun.id)
        (MLocalVar { ident; ty; span })
  | LFloat { value; ty; span } -> MFloat { value; ty; span }
  | LString { value; ty; span } -> MString { value; ty; span }
  | LInteger { value; ty; span } -> MInteger { value; ty; span }
  | LBoolean { value; ty; span } -> MBoolean { value; ty; span }
  | LUnit { ty; span } -> MUnit { ty; span }
  | LLambda { name; ty; span } -> MLambda { name; ty; span }
  | LApplication { lambda; arguement; ty; span } ->
      let lambda = monomorphize_expr env lambda in
      let arguement = monomorphize_expr env arguement in
      MApplication { lambda; arguement; ty; span }
      (* to make lets we are going to need a way to specify what the last statments should be wrapped in *)
  | LLet { name; name_ty; e1; e2; ty; span } ->
      let instances = ref [] in
      let instantiations =
        get_binders_with_type name
        |> List.map (fun (name, ty) -> (name, (ty, instances)))
        |> Env.of_list
      in
      let e1 = monomorphize_expr env e1 in
      let e2 = monomorphize_expr (Env.union instantiations env) e2 in
      MLet { name; name_ty; e1; e2; ty; span }
  | LLetRec { name; name_ty; e1; e2; ty; span } ->
      let instances = ref [] in
      let instantiations =
        get_binders_with_type name
        |> List.map (fun (name, ty) -> (name, (ty, instances)))
        |> Env.of_list
      in
      let env = Env.union instantiations env in
      let e1 = monomorphize_expr env e1 in
      let e2 = monomorphize_expr env e2 in
      MLetRec { name; name_ty; e1; e2; ty; span }
  | LIf { condition; consequent; alternative; ty; span } ->
      let condition = monomorphize_expr env condition in
      let consequent = monomorphize_expr env consequent in
      let alternative = monomorphize_expr env alternative in
      MIf { condition; consequent; alternative; ty; span }
  | LRecordAccess { record; projector; ty; span } ->
      let record = monomorphize_expr env record in
      MRecordAccess { record; projector; ty; span }
  | LRecordExtend { record; new_fields; ty; span } ->
      let record = monomorphize_expr env record in
      let new_fields =
        List.map
          (fun { label; value } ->
            let value = monomorphize_expr env value in
            { value; label })
          new_fields
      in
      MRecordExtend { record; new_fields; ty; span }
  | LRecord { fields; ty; span } ->
      let fields =
        List.map
          (fun { label; value } ->
            let value = monomorphize_expr env value in

            { value; label })
          fields
      in
      MRecord { fields; ty; span }
  | LMatch { value; cases; ty; span } ->
      let value = monomorphize_expr env value in
      let cases =
        List.map
          (fun { Ast.pattern; result } ->
            let result = monomorphize_expr env result in
            { Ast.pattern; result })
          cases
      in
      MMatch { value; cases; ty; span }
  | LConstructor { name; value; ty; span } ->
      let value = monomorphize_expr env value in
      MConstructor { name; value; ty; span }
  | LNominalConstructor { name; value; ty; span; id } ->
      let value = monomorphize_expr env value in
      MNominalConstructor { name; value; ty; span; id }

let monomorphize_tl env = function
  | LBind { name; name_ty; value; span } ->
      let instances = ref [] in
      let instantiations =
        get_binders_with_type name
        |> List.map (fun (name, ty) -> (name, (ty, instances)))
        |> Env.of_list
      in

      let value = monomorphize_expr env value in

      let env = Env.union instantiations env in
      (env, MBind { name; name_ty; value; span })
  | LRecBind { name; name_ty; value; span } ->
      let instances = ref [] in
      let instantiations =
        get_binders_with_type name
        |> List.map (fun (name, ty) -> (name, (ty, instances)))
        |> Env.of_list
      in
      let env = Env.union instantiations env in

      let value = monomorphize_expr env value in
      (env, MRecBind { name; name_ty; value; span })
  | LExpr expr ->
      let expr = monomorphize_expr env expr in
      (env, MExpr expr)
  | LPrintString s -> (env, MPrintString s)

let monomorphize_tls ?(env = Env.empty) tls =
  List.fold_left_map monomorphize_tl env tls |> snd
