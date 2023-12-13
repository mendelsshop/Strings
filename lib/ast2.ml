open Ast

type ast2 =
  | Float of float
  | Int of int
  | String of string
  | Ident of ident
  | InfixApplication of { infix : ident; arguements : ast2 * ast2 }
  | Application of { func : ast2; arguement : ast2 }
  | Function of { parameter : ident typed_opt option; abstraction : ast2 }
  | If of { condition : ast2; consequent : ast2; alternative : ast2 }
  | Let of { name : ident; value : ast2 }

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
  | Let { name; value } -> Let { name; value = ast_to_ast2 value }
  | Function { parameters; abstraction } ->
      curry_ify parameters (ast_to_ast2 abstraction)

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
  | Let { name; value } -> "let " ^ name ^ " = " ^ ast_to_string value
  | Function { parameter; abstraction } ->
      let param_to_string p =
        Option.map (fun ty -> p.value ^ ":" ^ type_to_string ty) p.ty
        |> Option.value ~default:p.value
      in
      "fun "
      ^ (parameter |> Option.fold ~some:param_to_string ~none:"")
      ^ "-> " ^ ast_to_string abstraction
