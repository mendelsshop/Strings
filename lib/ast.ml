open Types
open Utils

type 'a field = { label : string; value : 'a }
type 'a row = 'a field list
type ('a, 'b) case = { pattern : 'a; result : 'b }

type pattern =
  | PVar of { ident : string; span : AMPCL.span }
  | PNominalConstructor of { name : string; value : pattern; span : AMPCL.span }
  | PUnit of AMPCL.span
  | PWildcard of AMPCL.span
  | PFloat of { value : float; span : AMPCL.span }
  | PInteger of { value : int; span : AMPCL.span }
  | PBoolean of { value : bool; span : AMPCL.span }
  | PRecord of { fields : pattern row; span : AMPCL.span }
  (*   TODO: does record extension makes sense for patterns   *)
  | PConstructor of { name : string; value : pattern; span : AMPCL.span }
  | PAscribe of { pattern : pattern; ty : ty; span : AMPCL.span }
  | PString of { value : string; span : AMPCL.span }
  | POr of { patterns : pattern list; span : AMPCL.span }
  | PAs of { name : string; value : pattern; span : AMPCL.span }

type expr =
  | Var of { ident : string; span : AMPCL.span }
  | Lambda of { parameters : pattern list; body : expr; span : AMPCL.span }
  | Application of { lambda : expr; arguement : expr; span : AMPCL.span }
  | Let of { name : pattern; e1 : expr; e2 : expr; span : AMPCL.span }
  | LetRec of { name : pattern; e1 : expr; e2 : expr; span : AMPCL.span }
  | InfixApplication of {
      operator : string;
      left : expr;
      right : expr;
      span : AMPCL.span;
    }
  | Unit of AMPCL.span
  | String of { value : string; span : AMPCL.span }
  | Boolean of { value : bool; span : AMPCL.span }
  | Float of { value : float; span : AMPCL.span }
  | Integer of { value : int; span : AMPCL.span }
  | RecordAccess of { record : expr; projector : string; span : AMPCL.span }
  | RecordExtend of { record : expr; new_fields : expr row; span : AMPCL.span }
  | Record of { fields : expr row; span : AMPCL.span }
  | Constructor of { name : string; value : expr; span : AMPCL.span }
  | Match of {
      value : expr;
      cases : (pattern, expr) case list;
      span : AMPCL.span;
    }
  | If of {
      condition : expr;
      consequent : expr;
      alternative : expr;
      span : AMPCL.span;
    }
  | Ascribe of { value : expr; ty : ty; span : AMPCL.span }

type top_level =
  | Expr of expr
  | TypeBind of {
      name : string;
      ty_variables : StringSet.t;
      ty : ty;
      span : AMPCL.span;
    }
  | NominalTypeBind of {
      name : string;
      ty_variables : StringSet.t;
      ty : ty;
      span : AMPCL.span;
    }
  | Bind of { name : pattern; value : expr; span : AMPCL.span }
  | RecBind of { name : pattern; value : expr; span : AMPCL.span }
  | PrintString of string

let span_of_pattern : pattern -> AMPCL.span = function
  | PVar { span; _ }
  | PNominalConstructor { span; _ }
  | PUnit span
  | PWildcard span
  | PFloat { span; _ }
  | PInteger { span; _ }
  | PBoolean { span; _ }
  | PRecord { span; _ }
  | PConstructor { span; _ }
  | PAscribe { span; _ }
  | PString { span; _ }
  | POr { span; _ }
  | PAs { span; _ } ->
      span

let span_of_expr = function
  | Var { span; _ }
  | Float { span; _ }
  | String { span; _ }
  | Integer { span; _ }
  | Boolean { span; _ }
  | Lambda { span; _ }
  | Application { span; _ }
  | Unit span
  | Let { span; _ }
  | LetRec { span; _ }
  | If { span; _ }
  | RecordAccess { span; _ }
  | RecordExtend { span; _ }
  | Record { span; _ }
  | Match { span; _ }
  | InfixApplication { span; _ }
  | Ascribe { span; _ }
  | Constructor { span; _ } ->
      span

type program = top_level list

let list_to_string = String.concat " "

let rec pattern_to_string = function
  | PVar { ident; _ } -> ident
  | PString { value; _ } -> value
  | PUnit _ -> "()"
  | PBoolean { value; _ } -> string_of_bool value
  | PInteger { value; _ } -> string_of_int value
  | PFloat { value; _ } -> string_of_float value
  | PWildcard _ -> "_"
  | PRecord { fields; _ } ->
      "{ "
      ^ (fields
        |> List.map (fun { label; value } ->
               label ^ " = " ^ pattern_to_string value)
        |> String.concat "; ")
      ^ " }"
  | PConstructor { name; value; _ } ->
      "`" ^ name ^ " (" ^ pattern_to_string value ^ ")"
  | PNominalConstructor { name; value; _ } ->
      name ^ "nominal (" ^ pattern_to_string value ^ ")"
  | PAscribe _ -> failwith ""
  | PAs { name; value; _ } -> name ^ " as " ^ pattern_to_string value
  | POr { patterns; _ } ->
      List.map pattern_to_string patterns |> String.concat " | "

let rec expr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | Unit _ -> "()"
  | String { value; _ } -> value
  | Var { ident; _ } -> ident
  | Boolean { value; _ } -> string_of_bool value
  | Integer { value; _ } -> string_of_int value
  | Float { value; _ } -> string_of_float value
  | If { condition; consequent; alternative; _ } ->
      "if ( "
      ^ expr_to_string indent condition
      ^ " )\n" ^ indent_string ^ "then ( "
      ^ expr_to_string next_level consequent
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ expr_to_string next_level alternative
      ^ " )"
  | Let { name; e1; e2; _ } ->
      "let " ^ pattern_to_string name ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
      ^ " )"
  | LetRec { name; e1; e2; _ } ->
      "let rec " ^ pattern_to_string name ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
  | Lambda { parameters; body; _ } ->
      "\\"
      ^ list_to_string (List.map pattern_to_string parameters)
      ^ ".( " ^ expr_to_string indent body ^ " )"
  | Application { lambda; arguement; _ } ->
      "( "
      ^ expr_to_string indent lambda
      ^ " ) ( "
      ^ expr_to_string indent arguement
      ^ " )"
  | Record { fields; _ } ->
      "{\n"
      ^ (fields
        |> List.map (fun { label; value } ->
               indent_string ^ label ^ " = " ^ expr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordExtend { record; new_fields; _ } ->
      "{"
      ^ expr_to_string indent record
      ^ " with "
      ^ (new_fields
        |> List.map (fun { label; value } ->
               indent_string ^ label ^ " = " ^ expr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordAccess { record; projector; _ } ->
      expr_to_string indent record ^ "." ^ projector
  | Constructor { name; value; _ } ->
      name ^ " (" ^ expr_to_string indent value ^ ")"
  | Match { value; cases; _ } ->
      "match ( "
      ^ expr_to_string indent value
      ^ " ) with \n"
      ^ indent_string
        (* we have an indent before the first case as it does not get indented by concat *)
      ^ (cases
        |> List.map (fun { pattern; result } ->
               pattern_to_string pattern ^ " -> "
               ^ expr_to_string next_level result)
        |> String.concat ("\n" ^ indent_string ^ "|"))
  | InfixApplication { operator; left; right; _ } ->
      expr_to_string indent left ^ " " ^ operator ^ " "
      ^ expr_to_string indent right
  | Ascribe { value; _ } -> expr_to_string indent value

let expr_to_string = expr_to_string 0

let top_level_to_string = function
  | Expr e -> expr_to_string e
  | Bind { name; value; _ } ->
      "let " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | TypeBind { name; ty; ty_variables; _ } ->
      "type ("
      ^ (ty_variables |> StringSet.to_list |> String.concat ", ")
      ^ ") " ^ name ^ " = " ^ type_to_string ty
  | NominalTypeBind { name; ty; ty_variables; _ } ->
      "data ("
      ^ (ty_variables |> StringSet.to_list |> String.concat ", ")
      ^ ") " ^ name ^ " = " ^ type_to_string ty
  | RecBind { name; value; _ } ->
      "let rec " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | PrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
