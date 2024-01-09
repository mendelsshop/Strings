open Ast

type ast2 =
  | Float of float
  | Int of int
  | String of string
  | Ident of ident
  | InfixApplication of { infix : ident; arguements : ast2 * ast2 }
  | Application of { func : ast2; arguement : ast2 }
  | Function of { parameter : typed_ident option; abstraction : ast2 }
  | If of { condition : ast2; consequent : ast2; alternative : ast2 }
  | Let of { name : ident; e1 : ast2; e2 : ast2 }

type top_level =
  | Bind of { name : ident; value : ast2 }
  | PrintString of string

type program = top_level list

let rec curry_ify ps abs =
  match ps with
  | [] -> Function { parameter = None; abstraction = abs }
  | p :: [] -> Function { parameter = Some p; abstraction = abs }
  | p :: ps -> Function { parameter = Some p; abstraction = curry_ify ps abs }

let rec ast_to_ast2 (ast : ast) =
  match ast with
  | Float f -> Float f
  | Int f -> Int f
  | String f -> String f
  | Ident f -> Ident f
  | Application { func; arguement } ->
      Application { func = ast_to_ast2 func; arguement = ast_to_ast2 arguement }
  | InfixApplication { infix; arguements = e1, e2 } ->
      InfixApplication { infix; arguements = (ast_to_ast2 e1, ast_to_ast2 e2) }
  | If { condition; consequent; alternative } ->
      If
        {
          condition = ast_to_ast2 condition;
          consequent = ast_to_ast2 consequent;
          alternative = ast_to_ast2 alternative;
        }
  | Let { name; e1; e2 } ->
      Let { name; e1 = ast_to_ast2 e1; e2 = ast_to_ast2 e2 }
  | Function { parameters; abstraction } ->
      curry_ify parameters (ast_to_ast2 abstraction)

let ast_to_ast2 =
  List.map (fun (tl : Ast.top_level) ->
      match tl with
      | Bind { name; value } -> Bind { name; value = ast_to_ast2 value }
      | PrintString s -> PrintString s)

let rec ast_to_string ast =
  match ast with
  | Float f -> string_of_float f
  | Int i -> string_of_int i
  | String i -> i
  | Ident i -> i
  | InfixApplication { infix; arguements = e1, e2 } ->
      "( " ^ ast_to_string e1 ^ " " ^ infix ^ " " ^ ast_to_string e2 ^ " )"
  | Application { func; arguement } ->
      "( " ^ ast_to_string func ^ " " ^ ast_to_string arguement ^ " )"
  | If { condition; consequent; alternative } ->
      "if " ^ ast_to_string condition ^ " then " ^ ast_to_string consequent
      ^ " else " ^ ast_to_string alternative
  | Let { name; e1; e2 } ->
      "let " ^ name ^ " = " ^ ast_to_string e1 ^ " in " ^ ast_to_string e2
  | Function { parameter; abstraction } ->
      "fun "
      ^ Option.fold parameter ~some:(fun p -> p.ident) ~none:""
      ^ "-> " ^ ast_to_string abstraction

let print_top_level tl =
  match tl with
  | Bind { name; value } -> name ^ " = " ^ ast_to_string value ^ "\n"
  | PrintString s -> s

let print_program program =
  String.concat "\n" (List.map print_top_level program)
