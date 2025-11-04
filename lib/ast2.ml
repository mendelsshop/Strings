include Ast
open Types.Parsed
open Utils

type expr =
  | Var of { ident : string; span : AMPCL.span }
  | Lambda of { parameter : pattern; body : expr; span : AMPCL.span }
  | Application of { lambda : expr; arguement : expr; span : AMPCL.span }
  | Let of { name : pattern; e1 : expr; e2 : expr; span : AMPCL.span }
  | LetRec of { name : pattern; e1 : expr; e2 : expr; span : AMPCL.span }
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
  | Bind of { name : pattern; value : expr; span : AMPCL.span }
  | RecBind of { name : pattern; value : expr; span : AMPCL.span }
  | PrintString of string

type program = top_level list

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
  | Ascribe { span; _ }
  | Constructor { span; _ } ->
      span

let rec curry_ify ps body =
  match ps with
  | [] ->
      let span = span_of_expr body in
      Lambda
        {
          parameter = PUnit { start = span.start; finish = span.start };
          body;
          span;
        }
  | parameter :: [] ->
      let span = span_of_expr body in
      let span' = span_of_pattern parameter in
      Lambda { parameter; body; span = Utils.combine_spans span span' }
  | parameter :: ps ->
      let span' = span_of_pattern parameter in
      let body = curry_ify ps body in
      let span = span_of_expr body in
      Lambda { parameter; body; span = Utils.combine_spans span span' }

let rec ast_to_ast2 (ast : Ast.expr) =
  match ast with
  | Unit s -> Unit s
  | Float { value; span } -> Float { value; span }
  | Integer { value; span } -> Integer { value; span }
  | String { value; span } -> String { value; span }
  | Boolean { value; span } -> Boolean { value; span }
  | Var { ident; span } -> Var { ident; span }
  | Application { lambda; arguement; span } ->
      Application
        { lambda = ast_to_ast2 lambda; arguement = ast_to_ast2 arguement; span }
  | InfixApplication { operator; left; right; span } ->
      let left_span = Ast.span_of_expr left in
      let right_span = Ast.span_of_expr right in
      Application
        {
          lambda =
            Application
              {
                lambda =
                  Var
                    {
                      ident = operator;
                      span =
                        {
                          start = left_span.finish + 1;
                          finish = right_span.start - 1;
                        };
                    };
                arguement = ast_to_ast2 left;
                span =
                  { start = left_span.start; finish = right_span.start - 1 };
              };
          arguement = ast_to_ast2 right;
          span;
        }
  | If { condition; consequent; alternative; span } ->
      If
        {
          condition = ast_to_ast2 condition;
          consequent = ast_to_ast2 consequent;
          alternative = ast_to_ast2 alternative;
          span;
        }
  | LetRec { name; e1; e2; span } ->
      LetRec { name; e1 = ast_to_ast2 e1; e2 = ast_to_ast2 e2; span }
  | Let { name; e1; e2; span } ->
      Let { name; e1 = ast_to_ast2 e1; e2 = ast_to_ast2 e2; span }
      (* ignoreing the span means we ignore the "fun" part *)
  | Lambda { parameters; body; _ } -> curry_ify parameters (ast_to_ast2 body)
  | Record { fields; span } ->
      Record
        {
          fields =
            List.map
              (function
                | { label; value } -> { label; value = ast_to_ast2 value })
              fields;
          span;
        }
  | RecordExtend { record; new_fields; span } ->
      RecordExtend
        {
          record = ast_to_ast2 record;
          new_fields =
            List.map
              (function
                | { label; value } -> { label; value = ast_to_ast2 value })
              new_fields;
          span;
        }
  | Constructor { name; value; span } ->
      Constructor { name; value = ast_to_ast2 value; span }
  | Ascribe { value; ty; span } ->
      Ascribe { value = ast_to_ast2 value; ty; span }
  | RecordAccess { record; projector; span } ->
      RecordAccess { record = ast_to_ast2 record; projector; span }
  | Match { value; cases; span } ->
      Match
        {
          value = ast_to_ast2 value;
          cases =
            cases
            |> List.map (fun { pattern; result } ->
                { pattern; result = ast_to_ast2 result });
          span;
        }

let ast_to_ast2 =
  List.partition_map (fun (tl : Ast.top_level) ->
      match tl with
      | Bind { name; value; span } ->
          Bind { name; value = ast_to_ast2 value; span } |> Either.left
      | TypeBind { name; ty_variables; ty; span } ->
          Either.right
            (name, { Types.name; ty_variables; span; kind = Types.TypeDecl ty })
      | NominalTypeBind { name; id; ty_variables; ty; span } ->
          Either.right
            ( name,
              {
                Types.name;
                ty_variables;
                span;
                kind = Types.NominalTypeDecl { ty; id };
              } )
      | Expr e -> Expr (ast_to_ast2 e) |> Either.left
      | RecBind { name; value; span } ->
          RecBind { name; value = ast_to_ast2 value; span } |> Either.left
      | PrintString s -> PrintString s |> Either.left)

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
  | Lambda { parameter; body; _ } ->
      "\\"
      ^ pattern_to_string parameter
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
  | Ascribe { value; _ } -> expr_to_string indent value

let expr_to_string = expr_to_string 0

let top_level_to_string tl =
  match tl with
  | Expr e -> expr_to_string e
  | Bind { name; value; _ } ->
      "let " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | RecBind { name; value; _ } ->
      "let rec " ^ pattern_to_string name ^ " = " ^ expr_to_string value
  | PrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
