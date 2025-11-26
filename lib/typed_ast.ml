open Types
open Utils

type 't tpattern =
  | PTVar of { ident : string; ty : 't; span : AMPCL.span }
  | PTString of { value : string; ty : 't; span : AMPCL.span }
  | PTWildcard of { ty : 't; span : AMPCL.span }
  | PTInteger of { value : int; ty : 't; span : AMPCL.span }
  | PTFloat of { value : float; ty : 't; span : AMPCL.span }
  | PTBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | PTRecord of { fields : 't tpattern row; ty : 't; span : AMPCL.span }
  | PTConstructor of {
      name : string;
      value : 't tpattern;
      ty : 't;
      span : AMPCL.span;
    }
  | PTNominalConstructor of {
      name : string;
      value : 't tpattern;
      ty : 't;
      id : int;
      span : AMPCL.span;
    }
  | PTUnit of { ty : 't; span : AMPCL.span }
  | PTOr of { patterns : 't tpattern list; ty : 't; span : AMPCL.span }
  | PTAs of { name : string; value : 't tpattern; ty : 't; span : AMPCL.span }

let rec get_binders = function
  | PTVar { ident; _ } -> [ ident ]
  | PTString _ -> []
  | PTWildcard _ -> []
  | PTInteger _ -> []
  | PTFloat _ -> []
  | PTBoolean _ -> []
  | PTRecord { fields; _ } ->
      List.concat_map (fun { value; _ } -> get_binders value) fields
  | PTConstructor { value; _ } -> get_binders value
  | PTNominalConstructor { value; _ } -> get_binders value
  | PTAs { name; value; _ } -> name :: get_binders value
  | PTOr { patterns; _ } -> List.concat_map get_binders patterns
  | PTUnit _ -> []

let rec get_binders_with_type = function
  | PTVar { ident; ty; _ } -> [ (ident, ty) ]
  | PTString _ -> []
  | PTWildcard _ -> []
  | PTInteger _ -> []
  | PTFloat _ -> []
  | PTBoolean _ -> []
  | PTRecord { fields; _ } ->
      List.concat_map (fun { value; _ } -> get_binders_with_type value) fields
  | PTConstructor { value; _ } -> get_binders_with_type value
  | PTNominalConstructor { value; _ } -> get_binders_with_type value
  | PTAs { name; value; ty; _ } -> (name, ty) :: get_binders_with_type value
  | PTOr { patterns; _ } -> List.concat_map get_binders_with_type patterns
  | PTUnit _ -> []

type 't texpr =
  | TVar of { ident : string; ty : 't; span : AMPCL.span }
  | TFloat of { value : float; ty : 't; span : AMPCL.span }
  | TString of { value : string; ty : 't; span : AMPCL.span }
  | TInteger of { value : int; ty : 't; span : AMPCL.span }
  | TBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | TLambda of {
      parameter : 't tpattern;
      parameter_ty : 't;
      body : 't texpr;
      ty : 't;
      span : AMPCL.span;
    }
  | TApplication of {
      lambda : 't texpr;
      arguement : 't texpr;
      ty : 't;
      span : AMPCL.span;
    }
  | TUnit of { ty : 't; span : AMPCL.span }
  | TLet of {
      name : 't tpattern;
      name_ty : 't;
      e1 : 't texpr;
      e2 : 't texpr;
      ty : 't;
      span : AMPCL.span;
    }
  | TLetRec of {
      name : 't tpattern;
      name_ty : 't;
      e1 : 't texpr;
      e2 : 't texpr;
      ty : 't;
      span : AMPCL.span;
    }
  | TIf of {
      condition : 't texpr;
      consequent : 't texpr;
      alternative : 't texpr;
      ty : 't;
      span : AMPCL.span;
    }
  | TRecordAccess of {
      record : 't texpr;
      projector : string;
      ty : 't;
      span : AMPCL.span;
    }
  | TRecordExtend of {
      record : 't texpr;
      new_fields : 't texpr row;
      ty : 't;
      span : AMPCL.span;
    }
  | TRecord of { fields : 't texpr row; ty : 't; span : AMPCL.span }
  | TMatch of {
      value : 't texpr;
      cases : ('t tpattern, 't texpr) Ast.case list;
      ty : 't;
      span : AMPCL.span;
    }
  | TConstructor of {
      name : string;
      value : 't texpr;
      ty : 't;
      span : AMPCL.span;
    }
  | TNominalConstructor of {
      name : string;
      value : 't texpr;
      ty : 't;
      span : AMPCL.span;
      id : int;
    }

type 't top_level =
  | TBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't texpr;
      span : AMPCL.span;
    }
  | TRecBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't texpr;
      span : AMPCL.span;
    }
  | TPrintString of string
  | TExpr of 't texpr

let type_of_expr = function
  | TVar { ty; _ }
  | TFloat { ty; _ }
  | TString { ty; _ }
  | TInteger { ty; _ }
  | TBoolean { ty; _ }
  | TLambda { ty; _ }
  | TApplication { ty; _ }
  | TUnit { ty; _ }
  | TLet { ty; _ }
  | TLetRec { ty; _ }
  | TIf { ty; _ }
  | TRecordAccess { ty; _ }
  | TRecordExtend { ty; _ }
  | TRecord { ty; _ }
  | TMatch { ty; _ }
  | TConstructor { ty; _ }
  | TNominalConstructor { ty; _ } ->
      ty

type 't program = 't top_level list

let span_of_pattern : 't tpattern -> AMPCL.span = function
  | PTVar { span; _ }
  | PTNominalConstructor { span; _ }
  | PTUnit { span; _ }
  | PTWildcard { span; _ }
  | PTFloat { span; _ }
  | PTInteger { span; _ }
  | PTBoolean { span; _ }
  | PTRecord { span; _ }
  | PTConstructor { span; _ }
  | PTString { span; _ }
  | PTOr { span; _ }
  | PTAs { span; _ } ->
      span
(* we can make this non recursive if we make poly ast node store their type *)

let rec tpattern_to_string = function
  | PTVar { ident; ty; _ } -> ident ^ " : " ^ type_to_string ty
  | PTString { value; _ } -> value
  | PTUnit _ -> "()"
  | PTBoolean { value; _ } -> string_of_bool value
  | PTFloat { value; _ } -> string_of_float value
  | PTInteger { value; _ } -> string_of_int value
  | PTWildcard _ -> "_"
  | PTRecord { fields; _ } ->
      "{ "
      ^ (fields
        |> List.map (fun { label; value } ->
            label ^ " = " ^ tpattern_to_string value)
        |> String.concat "; ")
      ^ " }"
  | PTConstructor { name; value; _ } ->
      "`" ^ name ^ " (" ^ tpattern_to_string value ^ ")"
  | PTNominalConstructor { name; value; _ } ->
      name ^ " (" ^ tpattern_to_string value ^ ")"
  | PTAs { name; value; _ } -> name ^ " as " ^ tpattern_to_string value
  | PTOr { patterns; _ } ->
      List.map tpattern_to_string patterns |> String.concat " | "

let rec texpr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | TUnit _ -> "()"
  | TVar { ident; _ } -> ident
  | TString { value; _ } -> value
  | TInteger { value; _ } -> string_of_int value
  | TFloat { value; _ } -> string_of_float value
  | TBoolean { value; _ } -> string_of_bool value
  | TIf { condition; consequent; alternative; _ } ->
      "if ( "
      ^ texpr_to_string indent condition
      ^ " )\n" ^ indent_string ^ "then ( "
      ^ texpr_to_string next_level consequent
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ texpr_to_string next_level alternative
      ^ " )"
  | TLet { name; e1; e2; _ } ->
      "let " ^ tpattern_to_string name ^ " = ( " ^ texpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ texpr_to_string next_level e2
      ^ " )"
  | TLetRec { name; e1; e2; _ } ->
      "let rec " ^ tpattern_to_string name ^ " = ( " ^ texpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ texpr_to_string next_level e2
      ^ " )"
  | TLambda { parameter; body; _ } ->
      "\\"
      ^ tpattern_to_string parameter
      ^ ".( "
      ^ texpr_to_string indent body
      ^ " )"
  | TApplication { lambda; arguement; _ } ->
      "( "
      ^ texpr_to_string indent lambda
      ^ " ) ( "
      ^ texpr_to_string indent arguement
      ^ " )"
  | TRecord { fields; _ } ->
      "{\n"
      ^ (fields
        |> List.map (fun { label; value } ->
            indent_string ^ label ^ " = " ^ texpr_to_string next_level value)
        |> String.concat ";\n")
      ^ "\n}"
  | TRecordAccess { record; projector; _ } ->
      texpr_to_string indent record ^ "." ^ projector
  | TConstructor { name; value; _ } ->
      "`" ^ name ^ " (" ^ texpr_to_string indent value ^ ")"
  | TNominalConstructor { name; value; _ } ->
      name ^ " (" ^ texpr_to_string indent value ^ ")"
  | TMatch { value; cases; _ } ->
      "match ( "
      ^ texpr_to_string indent value
      ^ " ) with \n"
      ^ indent_string
        (* we have an indent before the first case as it does not get indented by concat *)
      ^ (cases
        |> List.map (fun { Ast.pattern; result } ->
            tpattern_to_string pattern ^ " -> "
            ^ texpr_to_string next_level result)
        |> String.concat ("\n" ^ indent_string ^ "|"))
  | TRecordExtend { record; new_fields; _ } ->
      "{"
      ^ texpr_to_string indent record
      ^ " with "
      ^ (new_fields
        |> List.map (fun { label; value } ->
            indent_string ^ label ^ " = " ^ texpr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"

let texpr_to_string = texpr_to_string 0

let top_level_to_string exp =
  match exp with
  | TExpr expr -> texpr_to_string expr
  | TRecBind { name; value; _ } ->
      "let rec " ^ tpattern_to_string name ^ " = " ^ texpr_to_string value
  | TBind { name; value; _ } ->
      "let (" ^ tpattern_to_string name ^ ") = " ^ texpr_to_string value
  | TPrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
