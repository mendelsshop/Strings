  open Ast

type ast2 =
  | Float of float
  | Int of int
  | String of string
  | Ident of ident
  | Application of { func : ast2; arguements : ast2 list }
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
  | Application { func; arguements } ->
      Application
        {
          func = ast_to_ast2 func;
          arguements = List.map ast_to_ast2 arguements;
        }
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
