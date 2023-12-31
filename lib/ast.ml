type ty = Function of (ty * ty) | Type of string | WildCard
type 'a typed_opt = { ty : ty option; value : 'a }
type ident = string

type ast =
  | Float of float
  | Int of int
  | String of string
  | Ident of ident
  | Application of { func : ast; arguement : ast }
  | InfixApplication of { infix : ident; arguements : ast * ast }
  | Function of { parameters : ident list; abstraction : ast }
  | If of { condition : ast; consequent : ast; alternative : ast }
  | Let of { name : ident; e1 : ast; e2 : ast }

type top_level = Bind of { name : ident; value : ast } | PrintString of string
type program = top_level list

let rec type_to_string ty =
  match ty with
  | WildCard -> "_"
  | Type t -> t
  | Function (t1, t2) ->
      "(" ^ type_to_string t1 ^ ") -> (" ^ type_to_string t2 ^ ")"

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
  | Let { name; e1; e2 } ->
      "let " ^ name ^ " = " ^ ast_to_string e1 ^ " in " ^ ast_to_string e2
  | Function { parameters; abstraction } ->
      "fun " ^ list_to_string parameters ^ "->" ^ ast_to_string abstraction

let print_program program =
  String.concat "\n"
    (List.map
       (fun exp ->
         match exp with
         | Bind { name; value } -> name ^ " = " ^ ast_to_string value ^ "\n"
         | PrintString s -> s)
       program)
