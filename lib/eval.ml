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

let apply f a =
  match f with
  | Function (env, f') -> f' env a
  (* TODO: maybe account for rec of rec *)
  | Rec { name; expr = Function (env, f') } -> f' ((name, f) :: env) a
  | _ -> error "cannot apply non function"

let get_bool b = match b with Bool b -> b | _ -> error "not bool"
let get_record r = match r with Record r -> r | _ -> error "not record"
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
  | Let { binding = PUnit _; e1; e2; _ } -> eval e1 >>= fun _ -> eval e2
  | Let { binding = PIdent { ident = name; _ }; e1; e2; _ } ->
      eval e1 >>= fun e1' -> scoped_insert (name, e1') (eval e2)
  | Function { parameter = PIdent { ident; _ }; abstraction; _ } ->
      fun s ->
        ( Function
            ( s,
              fun s x ->
                (insert (ident, x) >>= fun () -> eval abstraction) s |> fst ),
          s )
  | Ident { ident; _ } -> get ident
  | Application { func; arguement; _ } ->
      eval func >>= fun func' ->
      eval arguement <$> fun arguement' -> apply func' arguement'
  | If { condition; consequent; alternative; _ } ->
      eval condition >>= fun cond' ->
      eval (if get_bool cond' then consequent else alternative)
  | Poly { e; _ } -> eval e
  | Record r ->
      r.fields
      |> List.fold_left
           (fun rest { name; value } ->
             rest >>= fun rest ->
             eval value <$> fun value -> rest @ [ (name, value) ])
           ([] |> return)
      <$> fun fields -> Record fields
  | RecordAcces { value; projector; _ } ->
      eval value <$> fun value -> get_record value |> List.assoc projector
  | e ->
      print_endline ("todo: " ^ ast_to_string e);
      exit 1

let eval expr =
  match expr with
  | TypeBind _ -> return ()
  (* | Bind { name; value; _ } -> eval value >>= fun value' -> insert (name, value') *)
  | Bind { binding = PUnit _; value; _ } -> eval value <$> fun _ -> ()
  | Bind { binding = PIdent { ident = name; _ }; value; _ } ->
      eval value >>= fun value' -> insert (name, value')
  | PrintString s ->
      print_string s;
      return ()
  | e ->
      print_endline ("todo: " ^ top_level_to_string e);
      exit 1

let env =
  [
    ( "print",
      Function
        ( [],
          fun _ x ->
            print_ast x |> print_endline;
            Unit ) );
    ("=", Function ([], fun _ x -> Function ([], fun _ y -> Bool (x = y))));
    ( "*",
      Function
        ([], fun _ x -> Function ([], fun _ y -> Int (get_int x * get_int y)))
    );
    ( "-",
      Function
        ([], fun _ x -> Function ([], fun _ y -> Int (get_int x - get_int y)))
    );
  ]

let eval tls =
  List.fold_left (fun i tl -> i >>= fun _ -> eval tl) (return ()) tls
