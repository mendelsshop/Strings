open Typed_ast

let ( >>= ) (t : 's * 'm -> ('a * ('s * 'm)) option)
    (f : 'a -> 's * 'm -> ('b * ('s * 'm)) option) (s : 's * 'm) :
    ('b * ('s * 'm)) option =
  Option.bind (t s) (fun (a, s') -> f a s')

let bind = ( >>= )
let return a (s, m) = Some (a, (s, m))
let new_meta (s, m) = Some (Meta m, (s, m + 1))
let insert e (s, m) = Some ((), (e :: s, m))

let scoped_insert e f s =
  Option.map
    (fun (e', _) -> (e', s))
    (((fun (s, m) -> Option.some ((), (e :: s, m))) >>= fun _ -> f ()) s)

let get v (s, m) = Option.map (fun r -> (r, (s, m))) (List.assoc_opt v s)

let rec typify expr =
  match expr with
  | Ast2.Int i -> return (Int { ty = TInteger; value = i })
  | Ast2.Float i -> return (Float { ty = TFloat; value = i })
  | Ast2.String i -> return (String { ty = TString; value = i })
  | Ast2.Ident i -> get i >>= fun ty -> return (Ident { ty; ident = i })
  | Ast2.Function { parameter = Some { value; ty = None }; abstraction } ->
      new_meta >>= fun m ->
      scoped_insert (value, m) (fun () ->
          typify abstraction >>= fun abstraction ->
          new_meta >>= fun a_ty ->
          return
            (Function
               { abstraction; parameter = value; ty = TFunction (m, a_ty) }))
  | Ast2.If { condition; consequent; alternative } ->
      typify condition >>= fun condition ->
      typify consequent >>= fun consequent ->
      typify alternative >>= fun alternative ->
      new_meta >>= fun ty ->
      return (If { consequent; condition; alternative; ty })
  | Ast2.Application { func; arguement } ->
      typify func >>= fun func ->
      typify arguement >>= fun arguement ->
      new_meta >>= fun ty -> return (Application { func; arguement; ty })
  | Ast2.InfixApplication { infix; arguements = e1, e2 } ->
      typify e1 >>= fun e1 ->
      typify e2 >>= fun e2 ->
      new_meta >>= fun ty ->
      return (InfixApplication { infix; arguements = (e1, e2); ty })
  | Ast2.Function { parameter = None; abstraction } ->
      typify abstraction >>= fun abstraction ->
      new_meta >>= fun a_ty ->
      return
        (Function
           { abstraction; parameter = "()"; ty = TFunction (TUnit, a_ty) })
  | Ast2.Function _ -> exit 1 (* rn we dont allow type annotations *)
  | Ast2.Let { name; value } ->
      typify value >>= fun value ->
      insert (name, type_of value) >>= fun _ -> return value

let typify exp context = typify exp (context, 0)

(* let generate_constraints expr = match expr with *)
