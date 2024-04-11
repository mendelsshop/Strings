type eval_expr =
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Function of
      ((string * eval_expr) list
      * ((string * eval_expr) list -> eval_expr -> eval_expr))
  | Unit
  | Rec of { name : string; expr : eval_expr }
  | Record of (string * eval_expr) list
  | Tuple of eval_expr list

let print_ast expr =
  match expr with
  | Unit -> "()"
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Float f -> string_of_float f
  | String s -> s
  | Function _ -> "function"
  | Rec _ -> "rec"
  | Record _r -> "record"
  | Tuple _t -> "tuple"
