open Types

type ident = string
type typed_ident = { ident : ident; ty : ty option }
type 'b field = { name : string; value : 'b }
type ('a, 'b) projection = { value : 'a; projector : 'b }

type pattern =
  | PFloat of float
  | PInt of int
  | PTuple of pattern list
  | PRecord of pattern field list
  | PString of string
  | PIdent of ident
  | PConstructor of { name : string; value : pattern }
  | PUnit
  | PWildCard

type ast =
  | Float of float
  | Int of int
  (* tuples and record can be made into one form *)
  | Tuple of ast list
  | Record of ast field list
  | TupleAcces of (ast, int) projection
  | RecordAcces of (ast, string) projection
  | Constructor of { name : string; value : ast }
  | String of string
  | Ident of ident
  | Application of { func : ast; arguement : ast }
  | InfixApplication of { infix : ident; arguements : ast * ast }
  | Function of { parameters : typed_ident list; abstraction : ast }
  | If of { condition : ast; consequent : ast; alternative : ast }
  | Let of { name : ident; e1 : ast; e2 : ast }
  | LetRec of { name : ident; e1 : ast; e2 : ast }

type top_level =
  | TypeBind of { name : string; ty : ty }
  | Bind of { name : ident; value : ast }
  | RecBind of { name : ident; value : ast }
  | PrintString of string

type program = top_level list

let list_to_string = String.concat ""

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
  | LetRec { name; e1; e2 } ->
      "let rec  " ^ name ^ " = " ^ ast_to_string e1 ^ " in " ^ ast_to_string e2
  | Let { name; e1; e2 } ->
      "let " ^ name ^ " = " ^ ast_to_string e1 ^ " in " ^ ast_to_string e2
  | Function { parameters; abstraction } ->
      "fun "
      ^ list_to_string (List.map (fun p -> p.ident) parameters)
      ^ "->" ^ ast_to_string abstraction
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

let print_program program =
  String.concat "\n"
    (List.map
       (fun exp ->
         match exp with
         | Bind { name; value } -> "let " ^ name ^ " = " ^ ast_to_string value
         | TypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
         | RecBind { name; value } ->
             "let rec " ^ name ^ " = " ^ ast_to_string value
         | PrintString s -> s)
       program)
