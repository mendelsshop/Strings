open Ast
open Types

type ast2 =
  | Float of float
  | Int of int
  | String of string
  | Ident of ident
  | Application of { func : ast2; arguement : ast2 }
  | Function of { parameter : typed_ident option; abstraction : ast2 }
  | If of { condition : ast2; consequent : ast2; alternative : ast2 }
  | Let of { name : ident; e1 : ast2; e2 : ast2 }
  | LetRec of { name : ident; e1 : ast2; e2 : ast2 }
  (* tuples and record can be made into one form *)
  | Tuple of ast2 list
  | Record of ast2 field list
  | TupleAcces of (ast2, int) projection
  | RecordAcces of (ast2, string) projection
  | Constructor of { name : string; value : ast2 }

type top_level =
  | TypeBind of { name : string; ty : ty }
  | Bind of { name : ident; value : ast2 }
  | RecBind of { name : ident; value : ast2 }
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
      Application
        {
          func = Application { func = Ident infix; arguement = ast_to_ast2 e1 };
          arguement = ast_to_ast2 e2;
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
  | Function { parameters; abstraction } ->
      curry_ify parameters (ast_to_ast2 abstraction)
  | Tuple tuple -> Tuple (List.map ast_to_ast2 tuple)
  | Record record ->
      Record
        (List.map
           (function { name; value } -> { name; value = ast_to_ast2 value })
           record)
  | Constructor { name; value } ->
      Constructor { name; value = ast_to_ast2 value }
  | TupleAcces { projector; value } ->
      TupleAcces { projector; value = ast_to_ast2 value }
  | RecordAcces { projector; value } ->
      RecordAcces { projector; value = ast_to_ast2 value }

let ast_to_ast2 =
  List.map (fun (tl : Ast.top_level) ->
      match tl with
      | Bind { name; value } -> Bind { name; value = ast_to_ast2 value }
      | TypeBind { name; ty } -> TypeBind { name; ty }
      | RecBind { name; value } -> RecBind { name; value = ast_to_ast2 value }
      | PrintString s -> PrintString s)

let rec ast_to_string ast =
  match ast with
  | Float f -> string_of_float f
  | Int i -> string_of_int i
  | String i -> i
  | Ident i -> i
  | Application { func; arguement } ->
      "( " ^ ast_to_string func ^ " " ^ ast_to_string arguement ^ " )"
  | If { condition; consequent; alternative } ->
      "if " ^ ast_to_string condition ^ " then " ^ ast_to_string consequent
      ^ " else " ^ ast_to_string alternative
  | LetRec { name; e1; e2 } ->
      "let rec  " ^ name ^ " = " ^ ast_to_string e1 ^ " in " ^ ast_to_string e2
  | Let { name; e1; e2 } ->
      "let " ^ name ^ " = " ^ ast_to_string e1 ^ " in " ^ ast_to_string e2
  | Function { parameter; abstraction } ->
      "fun "
      ^ Option.fold parameter ~some:(fun p -> p.ident) ~none:""
      ^ "-> " ^ ast_to_string abstraction
  | Tuple tuple ->
      "( " ^ (tuple |> List.map ast_to_string |> String.concat " , ") ^ " )"
  | Record record ->
      "{ "
      ^ (record
        |> List.map (function { name; value } ->
               name ^ ": " ^ ast_to_string value)
        |> String.concat " , ")
      ^ " }"
  | TupleAcces { value; projector } ->
      ast_to_string value ^ "." ^ string_of_int projector
  | RecordAcces { value; projector } -> ast_to_string value ^ "." ^ projector
  | Constructor { name; value } -> name ^ " " ^ ast_to_string value

let print_top_level tl =
  match tl with
  | Bind { name; value } -> "let " ^ name ^ " = " ^ ast_to_string value
  | TypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
  | RecBind { name; value } -> "let rec " ^ name ^ " = " ^ ast_to_string value
  | PrintString s -> s

let print_program program =
  String.concat "\n" (List.map print_top_level program)
