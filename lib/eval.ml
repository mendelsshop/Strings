open Typed_ast
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
  let _, s' = insert v s in
  let e, _ = f s' in
  (e, s)

let apply f a =
  match f with
  | Function f' -> f' a
  | _ ->
      print_endline "cannot apply non function";
      exit 1

let get_bool b =
  match b with
  | Bool b -> b
  | _ ->
      print_endline "not bool";
      exit 1

let rec eval (expr : typed_ast) =
  match expr with
  | Unit _ -> return Unit
  | Float { value; _ } -> Float value |> return
  | Int { value; _ } -> Int value |> return
  | String { value; _ } -> String value |> return
  | Let { name; e1; e2; _ } ->
      eval e1 >>= fun e1' -> scoped_insert (name, e1') (eval e2)
  | Function { parameter = { ident; _ }; abstraction; _ } ->
      fun s ->
        ( Function
            (fun x ->
              (insert (ident, x) >>= fun () -> eval abstraction) s |> fst),
          s )
  | Ident { ident; _ } -> get ident
  | Application { func; arguement; _ } ->
      eval func >>= fun func' ->
      eval arguement <$> fun arguement' -> apply func' arguement'
  | Poly { e; _ } -> eval e
  | InfixApplication { infix = { ident; _ }; arguements = e1, e2; _ } ->
      get ident >>= fun infix ->
      eval e1 >>= fun e1' ->
      eval e2 <$> fun e2' -> apply infix e1' |> apply e2'
  | If { condition; consequent; alternative; _ } ->
      eval condition >>= fun cond' ->
      if get_bool cond' then eval consequent else eval alternative

let eval expr =
  match expr with
  | Bind { name; value; _ } -> eval value >>= fun value' -> insert (name, value')
  | PrintString s ->
      print_string s;
      return ()

let eval tls =
  List.fold_left (fun i tl -> i >>= fun _ -> eval tl) (return ()) tls
