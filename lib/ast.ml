open Types

type 'a field = { label : string; value : 'a }
type 'a row = 'a field list
type ('a, 'b) case = { pattern : 'a; result : 'b }

type pattern =
  | PVar of string
  | PUnit
  | PWildcard
  | PFloat of float
  | PInteger of int
  | PBoolean of bool
  | PRecord of pattern row
  (*   TODO: does record extension makes sense for patterns   *)
  | PConstructor of { name : string; value : pattern }
  | PAscribe of { pattern : pattern; ty : ty }
  | PString of string

type expr =
  | Var of string
  | Lambda of { parameters : pattern list; body : expr }
  | Application of { lambda : expr; arguement : expr }
  | Let of { name : pattern; e1 : expr; e2 : expr }
  | LetRec of { name : pattern; e1 : expr; e2 : expr }
  | InfixApplication of { operator : string; left : expr; right : expr }
  | Unit
  | String of string
  | Boolean of bool
  | Float of float
  | Integer of int
  | RecordAccess of { record : expr; projector : string }
  | RecordExtend of { record : expr; new_fields : expr row }
  | Record of expr row
  | Constructor of { name : string; value : expr }
  | Match of { value : expr; cases : (pattern, expr) case list }
  | If of { condition : expr; consequent : expr; alternative : expr }
  | Ascribe of { value : expr; ty : ty }

type top_level =
  | TypeBind of { name : string; ty : ty }
  | NominalTypeBind of { name : string; ty : ty }
  | Bind of { name : pattern; value : expr }
  | RecBind of { name : pattern; value : expr }
  | PrintString of string

type program = top_level list

let list_to_string = String.concat " "

let rec pattern_to_string = function
  | PVar s -> s
  | PString s -> s
  | PUnit -> "()"
  | PBoolean b -> string_of_bool b
  | PInteger n -> string_of_int n
  | PFloat n -> string_of_float n
  | PWildcard -> "_"
  | PRecord row ->
      "{ "
      ^ (row
        |> List.map (fun { label; value } ->
               label ^ " = " ^ pattern_to_string value)
        |> String.concat "; ")
      ^ " }"
  | PConstructor { name; value } -> name ^ " (" ^ pattern_to_string value ^ ")"
  | PAscribe _ -> failwith ""

let rec expr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | Unit -> "()"
  | String s -> s
  | Var s -> s
  | Boolean b -> string_of_bool b
  | Integer n -> string_of_int n
  | Float n -> string_of_float n
  | If { condition; consequent; alternative } ->
      "if ( "
      ^ expr_to_string indent condition
      ^ " )\n" ^ indent_string ^ "then ( "
      ^ expr_to_string next_level consequent
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ expr_to_string next_level alternative
      ^ " )"
  | Let { name; e1; e2 } ->
      "let " ^ pattern_to_string name ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
      ^ " )"
  | LetRec { name; e1; e2 } ->
      "let rec " ^ pattern_to_string name ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
  | Lambda { parameters; body } ->
      "\\"
      ^ list_to_string (List.map pattern_to_string parameters)
      ^ ".( " ^ expr_to_string indent body ^ " )"
  | Application { lambda; arguement } ->
      "( "
      ^ expr_to_string indent lambda
      ^ " ) ( "
      ^ expr_to_string indent arguement
      ^ " )"
  | Record row ->
      "{\n"
      ^ (row
        |> List.map (fun { label; value } ->
               indent_string ^ label ^ " = " ^ expr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordExtend { record; new_fields } ->
      "{"
      ^ expr_to_string indent record
      ^ " with "
      ^ (new_fields
        |> List.map (fun { label; value } ->
               indent_string ^ label ^ " = " ^ expr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordAccess { record; projector } ->
      expr_to_string indent record ^ "." ^ projector
  | Constructor { name; value } ->
      name ^ " (" ^ expr_to_string indent value ^ ")"
  | Match { value; cases } ->
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
  | InfixApplication { operator; left; right } ->
      expr_to_string indent left ^ " " ^ operator ^ " "
      ^ expr_to_string indent right
  | Ascribe { value; _ } -> expr_to_string indent value

let expr_to_string = expr_to_string 0

let top_level_to_string = function
  | Bind { name; value } ->
      "let " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | TypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
  | NominalTypeBind { name; ty } -> "data " ^ name ^ " = " ^ type_to_string ty
  | RecBind { name; value } ->
      "let rec " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | PrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
