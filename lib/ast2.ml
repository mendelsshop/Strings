include Ast
open Types

type expr =
  | Var of string
  | Lambda of pattern * expr
  | Application of expr * expr
  | Let of pattern * expr * expr
  | LetRec of pattern * expr * expr
  | Unit
  | Boolean of bool
  | String of string
  | Float of float
  | Integer of int
  | RecordAccess of expr * string
  | RecordExtend of expr * expr row
  | Record of expr row
  | Constructor of string * expr
  | Match of expr * (pattern * expr) list
  | Ascribe of (expr * ty)
  | If of expr * expr * expr

type top_level =
  | TypeBind of { name : string; ty : ty }
  | Bind of { name : pattern; value : expr }
  | RecBind of { name : pattern; value : expr }
  | PrintString of string

type program = top_level list

let rec curry_ify ps abs =
  match ps with
  | [] -> Lambda (PUnit, abs)
  | p :: [] -> Lambda (p, abs)
  | p :: ps -> Lambda (p, curry_ify ps abs)

let rec ast_to_ast2 (ast : Ast.expr) =
  match ast with
  | Unit -> Unit
  | Float f -> Float f
  | Boolean b -> Boolean b
  | Integer f -> Integer f
  | String f -> String f
  | Var f -> Var f
  | Application (func, arguement) ->
      Application (ast_to_ast2 func, ast_to_ast2 arguement)
  | InfixApplication (infix, e1, e2) ->
      Application (Application (Var infix, ast_to_ast2 e1), ast_to_ast2 e2)
  | If (condition, consequent, alternative) ->
      If (ast_to_ast2 condition, ast_to_ast2 consequent, ast_to_ast2 alternative)
  | LetRec (name, e1, e2) -> LetRec (name, ast_to_ast2 e1, ast_to_ast2 e2)
  | Let (name, e1, e2) -> Let (name, ast_to_ast2 e1, ast_to_ast2 e2)
  | Lambda (parameters, abstraction) ->
      curry_ify parameters (ast_to_ast2 abstraction)
  | Record record ->
      Record
        (List.map (function name, value -> (name, ast_to_ast2 value)) record)
  | RecordExtend (base, record) ->
      RecordExtend
        ( ast_to_ast2 base,
          List.map (function name, value -> (name, ast_to_ast2 value)) record )
  | Constructor (name, value) -> Constructor (name, ast_to_ast2 value)
  | Ascribe (expr, ty) -> Ascribe (ast_to_ast2 expr, ty)
  | RecordAccess (value, projector) ->
      RecordAccess (ast_to_ast2 value, projector)
  | Match (expr, cases) ->
      Match
        ( ast_to_ast2 expr,
          cases
          |> List.map (fun (pattern, result) -> (pattern, ast_to_ast2 result))
        )

let ast_to_ast2 =
  List.map (fun (tl : Ast.top_level) ->
      match tl with
      | Bind { name; value } -> Bind { name; value = ast_to_ast2 value }
      | TypeBind { name; ty } -> TypeBind { name; ty }
      | RecBind { name; value } -> RecBind { name; value = ast_to_ast2 value }
      | PrintString s -> PrintString s)

let rec expr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | Unit -> "()"
  | Var s -> s
  | String s -> s
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
      "\\" ^ pattern_to_string var ^ ".( " ^ expr_to_string indent abs ^ " )"
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
  | Ascribe (expr, _) -> expr_to_string indent expr

let expr_to_string = expr_to_string 0

let top_level_to_string tl =
  match tl with
  | Bind { name; value } ->
      "let " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | TypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
  | RecBind { name; value } ->
      "let rec " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | PrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
