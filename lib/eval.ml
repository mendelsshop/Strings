open Typed_ast
open Monads.Std
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

let rec matches_single (e : eval_expr) (case : Types.ty tpattern) =
  match (case, e) with
  | PTVar (v, _), p -> Some (Env.singleton v p)
  | PTRecord (r, _), Record r' ->
      List.map
        (fun (f, f_pat) ->
          let o = List.assoc_opt f r' in
          Option.bind o (fun e -> matches_single e f_pat))
        r
      |> List.fold_left
           (fun acc o -> Option.bind o (fun o -> Option.map (Env.union o) acc))
           (Some Env.empty)
  | PTConstructor (l, v, _), Constructor (l', v') when l == l' ->
      matches_single v' v
  | PTWildcard _, _ -> Some Env.empty
  | PTBoolean (v, _), Boolean v' when v = v' -> Some Env.empty
  | PTString (v, _), String v' when v = v' -> Some Env.empty
  | PTFloat (v, _), Float v' when v = v' -> Some Env.empty
  | PTInteger (v, _), Integer v' when v = v' -> Some Env.empty
  | PTUnit _, Unit -> Some Env.empty
  | _ -> None

let matches_single' e case = matches_single e case |> Option.get

let matches e cases =
  List.find_map
    (fun (pat, result) ->
      Option.map (fun binders -> (binders, result)) (matches_single e pat))
    cases
  |> Option.get

let apply f a =
  match f with
  | Function (env', f') ->
      let* env = M.get () in
      let m, _ = M.run (f' a) env' in
      let* _ = M.put env in
      return m
  | Rec (binders, Function (env', f')) ->
      let* env = M.get () in
      let binders = Env.map (fun e -> Rec (binders, e)) binders in
      let m, _ = M.run (f' a) (Env.union binders env') in
      let* _ = M.put env in
      return m
  (* TODO: maybe account for rec of rec *)
  (* | Rec { name; expr = Function (env, f') } -> f' ((name, f) :: env) a *)
  | _ -> error "cannot apply non function"

let get_bool b =
  match b with Boolean b | Rec (_, Boolean b) -> b | _ -> error "not bool"

let get_record r =
  match r with Record r | Rec (_, Record r) -> r | _ -> error "not record"

let get_int n =
  match n with Integer n | Rec (_, Integer n) -> n | _ -> error "not int"

let rec eval expr =
  match expr with
  | TUnit _ -> return Unit
  | TFloat (value, _) -> Float value |> return
  | TInteger (value, _) -> Integer value |> return
  | TString (value, _) -> String value |> return
  | TLet (PTUnit _, _, e1, e2, _) -> eval e1 >>= fun _ -> eval e2
  | TLet (binding, _, e1, e2, _) ->
      eval e1 >>= fun e1' ->
      scoped_insert (matches_single' e1' binding) (eval e2)
  | TLambda (parameter, _, abstraction, _) ->
      let* s = M.get () in
      return
        (Function
           ( s,
             fun x ->
               insert (matches_single' x parameter) >>= fun () ->
               eval abstraction ))
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
  | TLetRec (binding, _, e1, e2, _) ->
      let* e1' = eval e1 in
      let bindings = matches_single' e1' binding in
      let bindings = Env.map (fun e -> Rec (bindings, e)) bindings in
      scoped_insert bindings (eval e2)
  | TMatch (e, cases, _) ->
      let* e' = eval e in
      let binders, case = matches e' cases in
      scoped_insert binders (eval case)
  | TConstructor (l, e, _) ->
      let* e' = eval e in
      return (Constructor (l, e'))

let eval expr =
  match expr with
  | TTypeBind _ -> return ()
  | TBind { binding = PTUnit _; value; _ } -> eval value <$> fun _ -> ()
  | TBind { binding; value; _ } ->
      eval value >>= fun value' -> insert (matches_single' value' binding)
  | TPrintString s ->
      print_string s;
      return ()
  | TRecBind { binding; value } ->
      let* value' = eval value in
      let bindings = matches_single' value' binding in
      let bindings = Env.map (fun e -> Rec (bindings, e)) bindings in
      insert bindings

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
                 (Env.empty, fun y -> return (Integer (get_int x * get_int y))))
        ) );
    ( "-",
      Function
        ( Env.empty,
          fun x ->
            return
              (Function
                 (Env.empty, fun y -> return (Integer (get_int x - get_int y))))
        ) );
  ]
  |> Env.of_list

let eval tls =
  List.fold_left (fun i tl -> i >>= fun _ -> eval tl) (return ()) tls

let eval tls = M.run (eval tls) env
