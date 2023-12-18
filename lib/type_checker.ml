open Typed_ast

let ( >>= ) t f = Option.bind t (fun (t1, _) -> f t1)
let return t types = Some (t, types)

let rec type_checker expr =
  match expr with
  | Ast2.Int i -> return (Int i)
  | Ast2.Float f -> return (Float f)
  | Ast2.String s -> return (String s)
  | Ast2.Ident s ->
      fun types ->
        Option.map
          (fun ty -> (Ident { ty; value = s }, types))
          (List.assoc_opt s types)
  | Ast2.If { condition; consequent; alternative } ->
      fun types ->
        type_checker condition types >>= fun condition ->
        type_checker consequent types >>= fun consequent ->
        type_checker alternative types >>= fun alternative ->
        if
          type_of consequent <> type_of alternative || type_of condition <> Bool
        then None
        else
          Some
            ( If { ty = type_of consequent; condition; consequent; alternative },
              types )
  | Let { name; value } ->
      fun types ->
        type_checker value types >>= fun value ->
        Some
          ( Let { ty = type_of value; name; value },
            (name, type_of value) :: types )
  | Function { parameter = None; abstraction } ->
      fun types ->
        type_checker abstraction types >>= fun abstraction ->
        Some
          ( Function
              {
                ty = Function (Unit, type_of abstraction);
                parameter = None;
                abstraction;
              },
            types )
(* | Function { parameter = Some { value; ty = Some ty }; abstraction } -> *)
(*     fun types -> *)
(*       type_checker abstraction ((value, ty) :: types) *)
(*       >>= return (fun abstraction -> *)
(*               Function *)
(*                 { *)
(*                   ty = Function (ty, type_of abstraction); abstraction; *)
(*                   parameter = None; *)
(*                 }) *)
