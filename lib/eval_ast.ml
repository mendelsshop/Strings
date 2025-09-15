open Utils

type eval_expr =
  | Int of int
  | Boolean of bool
  | Float of float
  | String of string
  | Function of
      (eval_expr StringMap.t
      * (eval_expr ->
        (eval_expr, eval_expr StringMap.t) Monads.Std.Monad.State.t))
  | Unit
  (* | Rec of { name : string; expr : eval_expr } *)
  | Record of (string * eval_expr) list
  | Constructor of string * eval_expr

module Env = Env (struct
  type t = eval_expr
end)

let print_ast expr =
  match expr with
  | Unit -> "()"
  | Int i -> string_of_int i
  | Boolean b -> string_of_bool b
  | Float f -> string_of_float f
  | String s -> s
  | Function _ -> "function"
  (* | Rec _ -> "rec" *)
  | Record _r -> "record"
  | Constructor (label, _) -> label
