(* open Typed_ast *)

type eval_expr =
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Function of (eval_expr -> eval_expr)
  | Unit

let print_ast expr =
  match expr with
  | Unit -> "()"
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Float f -> string_of_float f
  | String s -> s
  | Function _ -> "function"
