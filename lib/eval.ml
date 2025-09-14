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
let insert v s = v @ s |> return ()

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

let rec get_bindings pattern expr =
  match (pattern, expr) with
  | PTVar (ident, _), _ -> [ (ident, expr) ]
  | ( ( PTFloat _ | PTInteger _ | PTString _ | PTUnit _ | PTWildcard _
      | PTBoolean _ ),
      _ ) ->
      []
  | PTRecord (pfields, _), Record fields ->
      pfields
      |> List.concat_map (fun (name, value) ->
             let value' = List.assoc name fields in
             get_bindings value value')
  | PTRecord _, _ -> error "not a record"
  | PTConstructor _, _ ->
      print_endline "todo: constructors";
      exit 1

let rec eval expr =
  match expr with
  (* | TRec { name; expr; _ } -> ( *)
  (*     eval expr <$> function *)
  (*     | Function _ as expr' -> Rec { name; expr = expr' } *)
  (*     | e -> e) *)
  | TUnit _ -> return Unit
  | TFloat (value, _) -> Float value |> return
  | TInteger (value, _) -> Int value |> return
  | TString (value, _) -> String value |> return
  | TLet (PTUnit _, _, e1, e2, _) -> eval e1 >>= fun _ -> eval e2
  | TLet (binding, _, e1, e2, _) ->
      eval e1 >>= fun e1' -> scoped_insert (get_bindings binding e1') (eval e2)
  | TLambda (parameter, _, abstraction, _) ->
      fun s ->
        ( Function
            ( s,
              fun s x ->
                ( insert (get_bindings parameter x) >>= fun () ->
                  eval abstraction )
                  s
                |> fst ),
          s )
  | TVar (ident, _) -> get ident
  | TApplication (func, arguement, _) ->
      eval func >>= fun func' ->
      eval arguement <$> fun arguement' -> apply func' arguement'
  | TIf (condition, consequent, alternative, _) ->
      eval condition >>= fun cond' ->
      eval (if get_bool cond' then consequent else alternative)
  | TRecord (fields, _) ->
      fields
      |> List.fold_left
           (fun rest (name, value) ->
             rest >>= fun rest ->
             eval value <$> fun value -> rest @ [ (name, value) ])
           ([] |> return)
      <$> fun fields -> Record fields
  | TRecordAccess (value, projector, _) ->
      eval value <$> fun value -> get_record value |> List.assoc projector
  | e ->
      print_endline ("todo: " ^ Typed_ast.texpr_to_string e);
      exit 1

let eval expr =
  match expr with
  | TTypeBind _ -> return ()
  | TBind { binding = PTUnit _; value; _ } -> eval value <$> fun _ -> ()
  | TBind { binding; value; _ } ->
      eval value >>= fun value' -> insert (get_bindings binding value')
  | TPrintString s ->
      print_string s;
      return ()
  | _ -> failwith "let rec"

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
