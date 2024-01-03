type ident = string

type ty =
  | Meta of int
  | TFunction of (ty * ty)
  | TUnit
  | TBool
  | TInteger
  | TFloat
  | TString

type 'a typed = { ty : ty; value : 'a }

let rec type_to_string ty =
  match ty with
  | Meta t -> "'" ^ string_of_int t
  | TString -> "string"
  | TFloat -> "float"
  | TUnit -> "()"
  | TBool -> "bool"
  | TInteger -> "int"
  | TFunction (t1, t2) ->
      "(" ^ type_to_string t1 ^ ") -> (" ^ type_to_string t2 ^ ")"

type typed_ast =
  | Unit of { ty : ty }
  | Float of { ty : ty; value : float }
  | Int of { ty : ty; value : int }
  | String of { ty : ty; value : string }
  | Ident of { ty : ty; ident : ident }
  | InfixApplication of {
      ty : ty;
      infix : ident;
      arguements : typed_ast * typed_ast;
    }
  | Application of { ty : ty; func : typed_ast; arguement : typed_ast }
  | Function of { ty : ty; parameter : ident; abstraction : typed_ast }
  | If of {
      ty : ty;
      condition : typed_ast;
      consequent : typed_ast;
      alternative : typed_ast;
    }
  | Let of { ty : ty; name : ident; value : typed_ast }

let type_of expr =
  match expr with
  | Int a -> a.ty
  | Float a -> a.ty
  | String a -> a.ty
  | Ident a -> a.ty
  | Unit a -> a.ty
  | If a -> a.ty
  | Function a -> a.ty
  | Application a -> a.ty
  | InfixApplication a -> a.ty
  | Let a -> a.ty

let rec ast_to_string ast =
  (match ast with
  | Unit _ -> "()"
  | Float { value; _ } -> string_of_float value
  | Int { value; _ } -> string_of_int value
  | String { value; _ } -> value
  | Ident { ident; _ } -> ident
  | InfixApplication { infix; arguements = e1, e2; _ } ->
      "( " ^ ast_to_string e1 ^ " " ^ infix ^ " " ^ ast_to_string e2 ^ " ) "
  | Application { func; arguement; _ } ->
      "( " ^ ast_to_string func ^ " " ^ ast_to_string arguement ^ " )"
  | If { condition; consequent; alternative; _ } ->
      "if " ^ ast_to_string condition ^ " then " ^ ast_to_string consequent
      ^ " else " ^ ast_to_string alternative
  | Let { name; value; _ } -> "let " ^ name ^ " = " ^ ast_to_string value
  | Function { parameter; abstraction; _ } ->
      "fun " ^ parameter ^ " -> " ^ ast_to_string abstraction)
  ^ ": " ^ (type_of ast |> type_to_string)
