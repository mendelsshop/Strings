open Types

type 'a row = (string * 'a) list

type pattern =
  | PVar of string
  | PUnit
  | PWildcard
  | PFloat of float
  | PInteger of int
  | PBoolean of bool
  | PRecord of pattern row
  (*   TODO: does record extension makes sense for patterns   *)
  | PConstructor of string * pattern
  | PAscribe of (pattern * ty)
  | PString of string

type expr =
  | Var of string
  | Lambda of pattern list * expr
  | Application of expr * expr
  | Let of pattern * expr * expr
  | LetRec of pattern * expr * expr
  | InfixApplication of (string * expr * expr)
  | Unit
  | String of string
  | Boolean of bool
  | Float of float
  | Integer of int
  | RecordAccess of expr * string
  | RecordExtend of expr * expr row
  | Record of expr row
  | Constructor of string * expr
  | Match of expr * (pattern * expr) list
  | If of expr * expr * expr
  | Ascribe of (expr * ty)

type top_level =
  | TypeBind of { name : string; ty : ty }
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
        |> List.map (fun (label, pat) -> label ^ " = " ^ pattern_to_string pat)
        |> String.concat "; ")
      ^ " }"
  | PConstructor (name, pattern) ->
      name ^ " (" ^ pattern_to_string pattern ^ ")"
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
  | If (cond, cons, alt) ->
      "if ( " ^ expr_to_string indent cond ^ " )\n" ^ indent_string ^ "then ( "
      ^ expr_to_string next_level cons
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ expr_to_string next_level alt
      ^ " )"
  | Let (var, e1, e2) ->
      "let " ^ pattern_to_string var ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
      ^ " )"
  | LetRec (var, e1, e2) ->
      "let rec " ^ pattern_to_string var ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
  | Lambda (var, abs) ->
      "\\"
      ^ list_to_string (List.map pattern_to_string var)
      ^ ".( " ^ expr_to_string indent abs ^ " )"
  | Application (abs, arg) ->
      "( " ^ expr_to_string indent abs ^ " ) ( " ^ expr_to_string indent arg
      ^ " )"
  | Record row ->
      "{\n"
      ^ (row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ expr_to_string indent pat)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordExtend (expr, row) ->
      "{" ^ expr_to_string indent expr ^ " with "
      ^ (row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ expr_to_string indent pat)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordAccess (record, label) -> expr_to_string indent record ^ "." ^ label
  | Constructor (name, expr) -> name ^ " (" ^ expr_to_string indent expr ^ ")"
  | Match (expr, cases) ->
      "match ( " ^ expr_to_string indent expr ^ " ) with \n"
      ^ indent_string
        (* we have an indent before the first case as it does not get indented by concat *)
      ^ (cases
        |> List.map (fun (pat, case) ->
               pattern_to_string pat ^ " -> " ^ expr_to_string next_level case)
        |> String.concat ("\n" ^ indent_string ^ "|"))
  | InfixApplication (infix, e1, e2) ->
      expr_to_string indent e1 ^ " " ^ infix ^ " " ^ expr_to_string indent e2
  | Ascribe (expr, _) -> expr_to_string indent expr

let expr_to_string = expr_to_string 0

let top_level_to_string = function
  | Bind { name; value } ->
      "let " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | TypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
  | RecBind { name; value } ->
      "let rec " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | PrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
