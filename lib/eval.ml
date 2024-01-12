open Eval_ast

let ( >>= ) t f s =
  let t', s' = t s in
  (f t') s'

let ( <$> ) t f s =
  let t', s' = t s in
  (f t', s')

let return e s = (e, s)
let bind = ( >>= )
let map = ( <$> )

(* type checker also checks for unbound variables so there is no need to do that here *)
let get e s = (List.assoc e s, s)
let insert v s = v :: s |> return ()

(* needed for let in *)
let scoped_insert v f s =
  ((fun s -> insert v s) >>= fun _ _ -> f () |> return s) s
