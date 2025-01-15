open Types

type ident = string
type typed_ident = { ident : ident; ty : ty option }
type 'b field = { name : string; value : 'b }
type ('a, 'b) projection = { value : 'a; projector : 'b }
type ('a, 'b) case = { pattern : 'a; result : 'b }

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
  | PAscribe of (pattern * ty)

type ast =
  | Float of float
  | Int of int
  (* tuples and record can be made into one form *)
  | Record of ast field list
  | RecordAcces of (ast, string) projection
  | Constructor of { name : string; value : ast }
  | String of string
  | Ident of ident
  | Application of { func : ast; arguement : ast }
  | InfixApplication of { infix : ident; arguements : ast * ast }
  | Function of { parameters : pattern list; abstraction : ast }
  | If of { condition : ast; consequent : ast; alternative : ast }
  | Let of { name : pattern; e1 : ast; e2 : ast }
  | LetRec of { name : string; e1 : ast; e2 : ast }
  | Match of { expr : ast; cases : (pattern, ast) case list }
  | Ascribe of (ast * ty)
  | Unit

type top_level =
  | TypeBind of { name : string; ty : ty }
  | Bind of { name : pattern; value : ast }
  | RecBind of { name : string; value : ast }
  | PrintString of string

type program = top_level list

let list_to_string = String.concat " "

let rec pattern_to_string pattern =
  match pattern with
  | PFloat f -> string_of_float f
  | PInt i -> string_of_int i
  | PRecord r ->
      "( "
      ^ (r
        |> List.map (fun { name; value } ->
               name ^ " = " ^ pattern_to_string value)
        |> String.concat ", ")
      ^ " )"
  | PString s -> "\"" ^ s ^ "\""
  | PIdent i -> i
  | PConstructor { name; value } -> name ^ "( " ^ pattern_to_string value ^ " )"
  | PUnit -> "()"
  | PWildCard -> "_"
  | PAscribe (pat, _) -> pattern_to_string pat

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
      "let " ^ pattern_to_string name ^ " = " ^ ast_to_string e1 ^ " in "
      ^ ast_to_string e2
  | Function { parameters; abstraction } ->
      "fun "
      ^ list_to_string (List.map pattern_to_string parameters)
      ^ "->" ^ ast_to_string abstraction
  | Record record ->
      "{ "
      ^ (record
        |> List.map (function { name; value } ->
               name ^ ": " ^ ast_to_string value)
        |> String.concat " , ")
      ^ " }"
  | RecordAcces { value; projector } -> ast_to_string value ^ "." ^ projector
  | Constructor { name; value } -> name ^ " " ^ ast_to_string value
  | Match { expr; cases } ->
      "match " ^ ast_to_string expr ^ " with "
      ^ String.concat " | "
          (cases
          |> List.map (fun { pattern; result } ->
                 pattern_to_string pattern ^ " -> " ^ ast_to_string result))
  | Ascribe (expr, _) -> ast_to_string expr
  | Unit -> "()"

let print_program program =
  String.concat "\n"
    (List.map
       (fun exp ->
         match exp with
         | Bind { name; value } ->
             "let " ^ pattern_to_string name ^ " = " ^ ast_to_string value
         | TypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
         | RecBind { name; value } ->
             "let rec " ^ name ^ " = " ^ ast_to_string value
         | PrintString s -> s)
       program)
