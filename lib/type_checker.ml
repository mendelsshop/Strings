open Typed_ast

let ( >>= ) (t : 's * 'm -> ('a * ('s * 'm)) option)
    (f : 'a -> 's * 'm -> ('b * ('s * 'm)) option) (s : 's * 'm) :
    ('b * ('s * 'm)) option =
  Option.bind (t s) (fun (a, s') -> f a s')

let bind = ( >>= )
let return a (s, m) = Some (a, (s, m))
let new_meta (s, m) = Some (m, (s, m + 1))
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
      scoped_insert (value, Meta m) (fun () ->
          typify abstraction >>= fun abstraction ->
          new_meta >>= fun a_ty ->
          return
            (Function
               {
                 abstraction;
                 parameter = value;
                 ty = TFunction (Meta m, Meta a_ty);
               }))
  | _ -> return (Unit { ty = TUnit })

let typify exp context = typify exp (context, 0)

(* let generate_constraints expr = match expr with *)
