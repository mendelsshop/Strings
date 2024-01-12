(* open Typed_ast *)

type eval_expr =
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Function of (eval_expr -> eval_expr)
  | Unit
