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
    (* we could probably do the same thing in the other asts (not having to constructor types) and just put an optional id if its nominal *)
  | Constructor of { name : string; value : eval_expr; id : int option }

module Env = Env.Make (String)

module EvalEnv = struct
  include Env

  type t = eval_expr Env.t
end

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
