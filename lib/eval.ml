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

let error msg =
  print_endline msg;
  exit 1

(* needed for let in *)
let scoped_insert v f s =
  let _, s' = insert v s in
  let e, _ = f s' in
  (e, s)

let apply f a env =
  match f with
  | Function f' -> f' env a
  (* TODO: maybe account for rec of rec *)
  | Rec { name; expr = Function f' } -> f' ((name, f) :: env) a
  | _ -> error "cannot apply non function"

let get_bool b = match b with Bool b -> b | _ -> error "not bool"
let get_int n = match n with Int n -> n | _ -> error "not int"

let rec eval (expr : typed_ast) =
  match expr with
  | Rec { name; expr; _ } -> (
      eval expr <$> function
      | Function _ as expr' -> Rec { name; expr = expr' }
      | e -> e)
  | Unit _ -> return Unit
  | Float { value; _ } -> Float value |> return
  | Int { value; _ } -> Int value |> return
  | String { value; _ } -> String value |> return
  | Let { name; e1; e2; _ } ->
      eval e1 >>= fun e1' -> scoped_insert (name, e1') (eval e2)
  | Function { parameter = { ident; _ }; abstraction; _ } ->
      return
        (Function
           (fun s x ->
             (insert (ident, x) >>= fun () -> eval abstraction) s |> fst))
  | Ident { ident; _ } -> get ident
  | Application { func; arguement; _ } ->
      fun s ->
        ( eval func >>= fun func' ->
          eval arguement <$> fun arguement' -> apply func' arguement' s )
          s
  | Poly { e; _ } -> eval e
  | If { condition; consequent; alternative; _ } ->
      eval condition >>= fun cond' ->
      eval (if get_bool cond' then consequent else alternative)

let eval expr =
  match expr with
  | Bind { name; value; _ } -> eval value >>= fun value' -> insert (name, value')
  | PrintString s ->
      print_string s;
      return ()

let env =
  [
    ( "print",
      Function
        (fun _ x ->
          print_ast x |> print_endline;
          Unit) );
    ("=", Function (fun _ x -> Function (fun _ y -> Bool (x = y))));
    ( "*",
      Function (fun _ x -> Function (fun _ y -> Int (get_int x * get_int y))) );
    ( "-",
      Function (fun _ x -> Function (fun _ y -> Int (get_int x - get_int y))) );
  ]

let eval tls =
  List.fold_left (fun i tl -> i >>= fun _ -> eval tl) (return ()) tls
