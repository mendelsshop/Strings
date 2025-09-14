open Typed_ast
include Monads.Std
open Eval_ast

module M = struct
  include Monad.State.T1 (Env) (Monad.Ident)
  include Monad.State.Make (Env) (Monad.Ident)
end

open M.Syntax
open M.Let

let ( <$> ) x f = M.map x ~f

(* type checker also checks for unbound variables so there is no need to do that here *)
let get e = M.gets (Env.find e)
let insert v = M.update (Env.union v)
let return = M.return

let error msg =
  print_endline msg;
  exit 1

(* needed for let in *)
let scoped_insert v f =
  let* env = M.get () in
  let* _ = insert v in
  let* v = f in
  let* _ = M.put env in
  return v

let apply f a =
  match f with
  | Function (env', f') ->
      let* env = M.get () in
      let m, _ = M.run (f' a) env' in
      let* _ = M.put env in
      return m
  (* TODO: maybe account for rec of rec *)
  (* | Rec { name; expr = Function (env, f') } -> f' ((name, f) :: env) a *)
  | _ -> error "cannot apply non function"

let get_bool b = match b with Boolean b -> b | _ -> error "not bool"
let get_record r = match r with Record r -> r | _ -> error "not record"
let get_int n = match n with Int n -> n | _ -> error "not int"

let rec get_bindings pattern expr =
  match (pattern, expr) with
  | PTVar (ident, _), _ -> Env.singleton ident expr
  | ( ( PTFloat _ | PTInteger _ | PTString _ | PTUnit _ | PTWildcard _
      | PTBoolean _ ),
      _ ) ->
      Env.empty
  | PTRecord (pfields, _), Record fields ->
      pfields
      |> List.fold_left
           (fun env (name, value) ->
             let value' = List.assoc name fields in
             Env.union (get_bindings value value') env)
           Env.empty
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
      let* s = M.get () in
      return
        (Function
           ( s,
             fun x ->
               insert (get_bindings parameter x) >>= fun () -> eval abstraction
           ))
  | TVar (ident, _) -> get ident
  | TApplication (func, arguement, _) ->
      let* func' = eval func in
      let* arguement' = eval arguement in
      apply func' arguement'
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
  | TBoolean (v, _) -> Boolean v |> return
  | TRecordExtend (r, fields', _) ->
      let* r' = eval r in
      let fields = get_record r' in
      let fields =
        List.fold_left
          (fun rest (name, value) ->
            rest >>= fun rest ->
            eval value <$> fun value -> rest @ [ (name, value) ])
          (fields |> return) fields'
      in
      fields <$> fun fields -> Record fields
  | TLetRec (_, _, _, _, _) -> failwith ""
  | TMatch (_, _, _) -> failwith ""
  | TConstructor (_, _, _) -> failwith ""
(* print_endline ("todo: " ^ Typed_ast.texpr_to_string e); *)
(* exit 1 *)

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
        ( Env.empty,
          fun x ->
            print_ast x |> print_endline;
            return Unit ) );
    ( "=",
      Function
        ( Env.empty,
          fun x ->
            return (Function (Env.empty, fun y -> return (Boolean (x = y)))) )
    );
    ( "*",
      Function
        ( Env.empty,
          fun x ->
            return
              (Function
                 (Env.empty, fun y -> return (Int (get_int x * get_int y)))) )
    );
    ( "-",
      Function
        ( Env.empty,
          fun x ->
            return
              (Function
                 (Env.empty, fun y -> return (Int (get_int x - get_int y)))) )
    );
  ]

let eval tls =
  List.fold_left (fun i tl -> i >>= fun _ -> eval tl) (return ()) tls
