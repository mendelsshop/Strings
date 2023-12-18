type ty = Function of (ty * ty) | String | Float | Integer | Unit | Bool
type 'a typed = { ty : ty; value : 'a }
type ident = string

let rec type_to_string ty =
  match ty with
  | String -> "string"
  | Float -> "float"
  | Unit -> "()"
  | Bool -> "bool"
  | Integer -> "int"
  | Function (t1, t2) ->
      "(" ^ type_to_string t1 ^ ") -> (" ^ type_to_string t2 ^ ")"

type typed_ast =
  | Float of float
  | Int of int
  | String of string
  | Ident of ident typed
  | InfixApplication of {
      ty : ty;
      infix : ident;
      arguements : typed_ast * typed_ast;
    }
  | Application of { ty : ty; func : typed_ast; arguement : typed_ast }
  | Function of {
      ty : ty;
      parameter : ident typed option;
      abstraction : typed_ast;
    }
  | If of {
      ty : ty;
      condition : typed_ast;
      consequent : typed_ast;
      alternative : typed_ast;
    }
  | Let of { ty : ty; name : ident; value : typed_ast }

let rec ast_to_string ast =
  match ast with
  | Float f -> string_of_float f
  | Int i -> string_of_int i
  | String i -> i
  | Ident i -> "( " ^ i.value ^ " : " ^ type_to_string i.ty ^ " )"
  | InfixApplication { infix; arguements = e1, e2; _ } ->
      "( " ^ ast_to_string e1 ^ " " ^ infix ^ " " ^ ast_to_string e2 ^ " )"
  | Application { func; arguement; _ } ->
      "( " ^ ast_to_string func ^ " " ^ ast_to_string arguement ^ " )"
  | If { condition; consequent; alternative; _ } ->
      "if " ^ ast_to_string condition ^ " then " ^ ast_to_string consequent
      ^ " else " ^ ast_to_string alternative
  | Let { name; value; _ } -> "let " ^ name ^ " = " ^ ast_to_string value
  | Function { parameter; abstraction; _ } ->
      let param_to_string p = p.value ^ ":" ^ type_to_string p.ty in
      "fun "
      ^ (parameter |> Option.fold ~some:param_to_string ~none:"")
      ^ "-> " ^ ast_to_string abstraction

(* assumes the expression has been type checked already ie there cannot be different types for if's consequent and alternative *)
let type_of expr =
  match expr with
  | Int _ -> Integer
  | Float _ -> Float
  | String _ -> String
  | Ident { ty; _ } -> ty
  | If { ty; _ } -> ty
  | Let { ty; _ } -> ty
  | Function { ty; _ } -> ty
  | Application { ty; _ } -> ty
  | InfixApplication { ty; _ } -> ty
