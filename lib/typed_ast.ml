open Types

type 't tpattern =
  | PTVar of { ident : string; ty : 't }
  | PTString of { value : string; ty : 't }
  | PTWildcard of 't
  | PTInteger of { value : int; ty : 't }
  | PTFloat of { value : float; ty : 't }
  | PTBoolean of { value : bool; ty : 't }
  | PTRecord of { fields : 't tpattern Ast.row; ty : 't }
  | PTConstructor of { name : string; value : 't tpattern; ty : 't }
  | PTNominalConstructor of {
      name : string;
      value : 't tpattern;
      ty : 't;
      id : int;
    }
  | PTUnit of 't
  | PTOr of { patterns : 't tpattern list; ty : 't }
  | PTAs of { name : string; value : 't tpattern; ty : 't }

type 't texpr =
  | TVar of { ident : string; ty : ty }
  | TFloat of { value : float; ty : ty }
  | TString of { value : string; ty : ty }
  | TInteger of { value : int; ty : ty }
  | TBoolean of { value : bool; ty : ty }
  | TLambda of {
      parameter : 't tpattern;
      parameter_ty : 't;
      body : 't texpr;
      ty : ty;
    }
  | TApplication of { lambda : 't texpr; arguement : 't texpr; ty : ty }
  | TUnit of 't
  | TLet of {
      name : 't tpattern;
      name_ty : 't;
      e1 : 't texpr;
      e2 : 't texpr;
      ty : ty;
    }
  | TLetRec of {
      name : 't tpattern;
      name_ty : 't;
      e1 : 't texpr;
      e2 : 't texpr;
      ty : ty;
    }
  | TIf of {
      condition : 't texpr;
      consequent : 't texpr;
      alternative : 't texpr;
      ty : ty;
    }
  | TRecordAccess of { record : 't texpr; projector : string; ty : ty }
  | TRecordExtend of {
      record : 't texpr;
      new_fields : 't texpr Ast.row;
      ty : ty;
    }
  | TRecord of { fields : 't texpr Ast.row; ty : ty }
  | TMatch of {
      value : 't texpr;
      cases : ('t tpattern, 't texpr) Ast.case list;
      ty : ty;
    }
  | TConstructor of { name : string; value : 't texpr; ty : ty }
  | TNominalConstructor of {
      name : string;
      value : 't texpr;
      ty : ty;
      id : int;
    }

type 't top_level =
  | TBind of { name : 't tpattern; value : 't texpr }
  | TRecBind of { name : 't tpattern; value : 't texpr }
  | TTypeBind of { name : string; ty : ty }
  | TPrintString of string

let type_of_expr = function
  | TVar { ty; _ }
  | TFloat { ty; _ }
  | TString { ty; _ }
  | TInteger { ty; _ }
  | TBoolean { ty; _ }
  | TLambda { ty; _ }
  | TApplication { ty; _ }
  | TUnit ty
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

(* we can make this non recursive if we make poly ast node store their type *)

let rec tpattern_to_string = function
  | PTVar { ident; ty } -> ident ^ " : " ^ type_to_string ty
  | PTString { value; _ } -> value
  | PTUnit _ -> "()"
  | PTBoolean { value; _ } -> string_of_bool value
  | PTFloat { value; _ } -> string_of_float value
  | PTInteger { value; _ } -> string_of_int value
  | PTWildcard _ -> "_"
  | PTRecord { fields; _ } ->
      "{ "
      ^ (fields
        |> List.map (fun { Ast.label; value } ->
               label ^ " = " ^ tpattern_to_string value)
        |> String.concat "; ")
      ^ " }"
  | PTConstructor { name; value; _ } ->
      name ^ " (" ^ tpattern_to_string value ^ ")"
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
        |> List.map (fun { Ast.label; value } ->
               indent_string ^ label ^ " = " ^ texpr_to_string next_level value)
        |> String.concat ";\n")
      ^ "\n}"
  | TRecordAccess { record; projector; _ } ->
      texpr_to_string indent record ^ "." ^ projector
  | TConstructor { name; value; _ } ->
      name ^ " (" ^ texpr_to_string indent value ^ ")"
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
        |> List.map (fun { Ast.label; value } ->
               indent_string ^ label ^ " = " ^ texpr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"

let texpr_to_string = texpr_to_string 0

let top_level_to_string exp =
  match exp with
  | TTypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
  | TRecBind { name; value } ->
      "let rec " ^ tpattern_to_string name ^ " = " ^ texpr_to_string value
  | TBind { name; value } ->
      "let (" ^ tpattern_to_string name ^ ") = " ^ texpr_to_string value
  | TPrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
