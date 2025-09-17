include Ast
open Types

type expr =
  | Var of string
  | Lambda of { parameter : pattern; body : expr }
  | Application of { lambda : expr; arguement : expr }
  | Let of { name : pattern; e1 : expr; e2 : expr }
  | LetRec of { name : pattern; e1 : expr; e2 : expr }
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
  | Bind of { name : pattern; value : expr }
  | RecBind of { name : pattern; value : expr }
  | PrintString of string

type program = top_level list

let rec curry_ify ps body =
  match ps with
  | [] -> Lambda { parameter = PUnit; body }
  | parameter :: [] -> Lambda { parameter; body }
  | parameter :: ps -> Lambda { parameter; body = curry_ify ps body }

let rec ast_to_ast2 (ast : Ast.expr) =
  match ast with
  | Unit -> Unit
  | Float f -> Float f
  | Boolean b -> Boolean b
  | Integer f -> Integer f
  | String f -> String f
  | Var f -> Var f
  | Application { lambda; arguement } ->
      Application
        { lambda = ast_to_ast2 lambda; arguement = ast_to_ast2 arguement }
  | InfixApplication { operator; left; right } ->
      Application
        {
          lambda =
            Application { lambda = Var operator; arguement = ast_to_ast2 left };
          arguement = ast_to_ast2 right;
        }
  | If { condition; consequent; alternative } ->
      If
        {
          condition = ast_to_ast2 condition;
          consequent = ast_to_ast2 consequent;
          alternative = ast_to_ast2 alternative;
        }
  | LetRec { name; e1; e2 } ->
      LetRec { name; e1 = ast_to_ast2 e1; e2 = ast_to_ast2 e2 }
  | Let { name; e1; e2 } ->
      Let { name; e1 = ast_to_ast2 e1; e2 = ast_to_ast2 e2 }
  | Lambda { parameters; body } -> curry_ify parameters (ast_to_ast2 body)
  | Record record ->
      Record
        (List.map
           (function { label; value } -> { label; value = ast_to_ast2 value })
           record)
  | RecordExtend { record; new_fields } ->
      RecordExtend
        {
          record = ast_to_ast2 record;
          new_fields =
            List.map
              (function
                | { label; value } -> { label; value = ast_to_ast2 value })
              new_fields;
        }
  | Constructor { name; value } ->
      Constructor { name; value = ast_to_ast2 value }
  | Ascribe { value; ty } -> Ascribe { value = ast_to_ast2 value; ty }
  | RecordAccess { record; projector } ->
      RecordAccess { record = ast_to_ast2 record; projector }
  | Match { value; cases } ->
      Match
        {
          value = ast_to_ast2 value;
          cases =
            cases
            |> List.map (fun { pattern; result } ->
                   { pattern; result = ast_to_ast2 result });
        }

let ast_to_ast2 =
  List.filter_map (fun (tl : Ast.top_level) ->
      match tl with
      | Bind { name; value } ->
          Bind { name; value = ast_to_ast2 value } |> Option.some
      | TypeBind _ -> None
      | NominalTypeBind _ -> None
      | RecBind { name; value } ->
          RecBind { name; value = ast_to_ast2 value } |> Option.some
      | PrintString s -> PrintString s |> Option.some)

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
  | Lambda { parameter; body } ->
      "\\"
      ^ pattern_to_string parameter
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
  | Ascribe { value; _ } -> expr_to_string indent value

let expr_to_string = expr_to_string 0

let top_level_to_string tl =
  match tl with
  | Bind { name; value } ->
      "let " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | RecBind { name; value } ->
      "let rec " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | PrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
