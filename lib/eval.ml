open Typed_ast
open Utils
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
  | PTVar { ident; _ }, p -> Some (Env.singleton ident p)
  | PTRecord { fields; _ }, Record r' ->
      List.map
        (fun { Ast.label; value } ->
          let o = StringMap.find_opt label r' in
          Option.bind o (fun e -> matches_single e value))
        fields
      |> List.fold_left
           (fun acc o -> Option.bind o (fun o -> Option.map (Env.union o) acc))
           (Some Env.empty)
  | ( PTNominalConstructor { name; value; id; _ },
      Constructor { name = name'; value = value'; id = Some id' } )
    when name = name' && id = id' ->
      matches_single value' value
  | ( PTConstructor { name; value; _ },
      Constructor { name = name'; value = value'; id = None } )
    when name == name' ->
      matches_single value' value
  | PTWildcard _, _ -> Some Env.empty
  | PTBoolean { value; _ }, Boolean v' when value = v' -> Some Env.empty
  | PTString { value; _ }, String v' when value = v' -> Some Env.empty
  | PTFloat { value; _ }, Float v' when value = v' -> Some Env.empty
  | PTInteger { value; _ }, Integer v' when value = v' -> Some Env.empty
  | PTUnit _, Unit -> Some Env.empty
  | _ -> None

let matches_single' e case = matches_single e case |> Option.get

let matches e cases =
  List.find_map
    (fun { Ast.pattern; result } ->
      Option.map (fun binders -> (binders, result)) (matches_single e pattern))
    cases
  |> Option.get

(* TODO: for apply/get_* or other places where there are recs allow unwinding of multiple recs also applies to matching *)
let apply f a =
  match f with
  | Function { envoirnment = envoirnment'; lambda } ->
      let* env = M.get () in
      let m, _ = M.run (lambda a) envoirnment' in
      let* _ = M.put env in
      return m
  | Rec
      {
        rec_envoirnment;
        value = Function { envoirnment = envoirnment'; lambda };
      } ->
      let* env = M.get () in
      let binders =
        Env.map (fun e -> Rec { rec_envoirnment; value = e }) rec_envoirnment
      in
      let m, _ = M.run (lambda a) (Env.union binders envoirnment') in
      let* _ = M.put env in
      return m
  | _ -> error "cannot apply non function"

let get_bool b =
  match b with
  | Boolean b | Rec { value = Boolean b; _ } -> b
  | _ -> error "not bool"

let get_record r =
  match r with
  | Record r | Rec { value = Record r; _ } -> r
  | _ -> error "not record"

let get_int n =
  match n with
  | Integer n | Rec { value = Integer n; _ } -> n
  | _ -> error "not int"

let rec eval expr =
  match expr with
  | TUnit _ -> return Unit
  | TFloat { value; _ } -> Float value |> return
  | TInteger { value; _ } -> Integer value |> return
  | TString { value; _ } -> String value |> return
  | TLet { name = PTUnit _; e1; e2; _ } -> eval e1 >>= fun _ -> eval e2
  | TLet { name; e1; e2; _ } ->
      eval e1 >>= fun e1' -> scoped_insert (matches_single' e1' name) (eval e2)
  | TLambda { parameter; body; _ } ->
      let* s = M.get () in
      return
        (Function
           {
             envoirnment = s;
             lambda =
               (fun x ->
                 insert (matches_single' x parameter) >>= fun () -> eval body);
           })
  | TVar { ident; _ } -> get ident
  | TApplication { lambda; arguement; _ } ->
      let* func' = eval lambda in
      let* arguement' = eval arguement in
      apply func' arguement'
  | TIf { condition; consequent; alternative; _ } ->
      eval condition >>= fun cond' ->
      eval (if get_bool cond' then consequent else alternative)
  | TRecord { fields; _ } ->
      fields
      |> List.fold_left
           (fun rest { Ast.label; value } ->
             rest >>= fun rest ->
             eval value <$> fun value -> StringMap.add label value rest)
           (StringMap.empty |> return)
      <$> fun fields -> Record fields
  | TRecordAccess { record; projector; _ } ->
      eval record <$> fun value -> get_record value |> StringMap.find projector
  | TBoolean { value; _ } -> Boolean value |> return
  | TRecordExtend { record; new_fields; _ } ->
      let* r' = eval record in
      let fields = get_record r' in
      let fields =
        List.fold_left
          (fun rest { Ast.label; value } ->
            rest >>= fun rest ->
            eval value <$> fun value -> StringMap.add label value rest)
          (fields |> return) new_fields
      in
      fields <$> fun fields -> Record fields
  | TLetRec { name; e1; e2; _ } ->
      let* e1' = eval e1 in
      let rec_envoirnment = matches_single' e1' name in
      let bindings =
        Env.map (fun value -> Rec { rec_envoirnment; value }) rec_envoirnment
      in
      scoped_insert bindings (eval e2)
  | TMatch { value; cases; _ } ->
      let* e' = eval value in
      let binders, case = matches e' cases in
      scoped_insert binders (eval case)
  | TConstructor { name; value; _ } ->
      let* value = eval value in
      return (Constructor { name; value; id = None })
  | TNominalConstructor { name; value; id; _ } ->
      let* value = eval value in
      return (Constructor { name; value; id = Some id })

let eval expr =
  match expr with
  | TTypeBind _ -> return ()
  | TBind { name = PTUnit _; value; _ } -> eval value <$> fun _ -> ()
  | TBind { name; value; _ } ->
      eval value >>= fun value' -> insert (matches_single' value' name)
  | TPrintString s ->
      print_string s;
      return ()
  | TRecBind { name; value } ->
      let* value' = eval value in
      let rec_envoirnment = matches_single' value' name in
      let bindings =
        Env.map (fun value -> Rec { rec_envoirnment; value }) rec_envoirnment
      in
      insert bindings

let env =
  [
    ( "print",
      Function
        {
          envoirnment = Env.empty;
          lambda =
            (fun x ->
              print_ast x |> print_endline;
              return Unit);
        } );
    ( "=",
      Function
        {
          envoirnment = Env.empty;
          lambda =
            (fun x ->
              return
                (Function
                   {
                     envoirnment = Env.empty;
                     lambda = (fun y -> return (Boolean (x = y)));
                   }));
        } );
    ( "*",
      Function
        {
          envoirnment = Env.empty;
          lambda =
            (fun x ->
              return
                (Function
                   {
                     envoirnment = Env.empty;
                     lambda =
                       (fun y -> return (Integer (get_int x * get_int y)));
                   }));
        } );
    ( "-",
      Function
        {
          envoirnment = Env.empty;
          lambda =
            (fun x ->
              return
                (Function
                   {
                     envoirnment = Env.empty;
                     lambda =
                       (fun y -> return (Integer (get_int x - get_int y)));
                   }));
        } );
  ]
  |> Env.of_list

let eval tls =
  List.fold_left (fun i tl -> i >>= fun _ -> eval tl) (return ()) tls

let eval tls = M.run (eval tls) env
