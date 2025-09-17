open Utils

type eval_expr =
  | Integer of int
  | Boolean of bool
  | Float of float
  | String of string
  | Function of {
      envoirnment : eval_expr StringMap.t;
      lambda :
        eval_expr -> (eval_expr, eval_expr StringMap.t) Monads.Std.Monad.State.t;
    }
  | Unit
  | Rec of { rec_envoirnment : eval_expr StringMap.t; value : eval_expr }
  | Record of eval_expr StringMap.t
  | Constructor of { name : string; value : eval_expr }

module Env = Env.Make (struct
  type t = eval_expr
end)

let print_ast expr =
  match expr with
  | Unit -> "()"
  | Integer i -> string_of_int i
  | Boolean b -> string_of_bool b
  | Float f -> string_of_float f
  | String s -> s
  | Function _ -> "function"
  | Rec _ -> "rec"
  | Record _r -> "record"
  | Constructor { name; _ } -> name
