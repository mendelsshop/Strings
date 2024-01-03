open Typed_ast

let ( >>= ) (t : 's * 'm -> ('a * ('s * 'm)) option)
    (f : 'a -> 's * 'm -> ('b * ('s * 'm)) option) (s : 's * 'm) :
    ('b * ('s * 'm)) option =
  Option.bind (t s) (fun (a, s') -> f a s')

let bind = ( >>= )
let return a (s, m) = Some (a, (s, m))
let new_meta (s, m) = Some (Meta m, (s, m + 1))
let insert e (s, m) = Some ((), (e :: s, m))

(* scoped insert allows temporary insertion, but the meta variable created are not temporary *)
let scoped_insert e f (s, m) =
  Option.map
    (fun (e', (_, m')) -> (e', (s, m')))
    (((fun (s, m) -> Option.some ((), (e :: s, m))) >>= fun _ -> f ()) (s, m))

let get v (s, m) = Option.map (fun r -> (r, (s, m))) (List.assoc_opt v s)

let rec typify expr =
  match expr with
  | Ast2.Int i -> return (Int { ty = TInteger; value = i })
  | Ast2.Float i -> return (Float { ty = TFloat; value = i })
  | Ast2.String i -> return (String { ty = TString; value = i })
  | Ast2.Ident i -> get i >>= fun ty -> return (Ident { ty; ident = i })
  | Ast2.Function { parameter = Some { value; ty = None }; abstraction } ->
      new_meta >>= fun m ->
      new_meta >>= fun a_ty ->
      scoped_insert (value, m) (fun () ->
          typify abstraction >>= fun abstraction ->
          return
            (Function
               { abstraction; parameter = { ident = value; ty = m }; ty = a_ty }))
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
      (* 1: we should get the lookup/use/have the type for infix which leads to 2: we should remove infix not from ast and make it expand to regular application. *)
      typify e1 >>= fun e1 ->
      typify e2 >>= fun e2 ->
      get infix >>= fun f_ty ->
      new_meta >>= fun ty ->
      return
        (InfixApplication
           { infix = { ident = infix; ty = f_ty }; arguements = (e1, e2); ty })
  | Ast2.Function { parameter = None; abstraction } ->
      typify abstraction >>= fun abstraction ->
      new_meta >>= fun a_ty ->
      return
        (Function
           {
             abstraction;
             parameter = { ident = "()"; ty = TUnit };
             ty = TFunction (TUnit, a_ty);
           })
  | Ast2.Function _ -> exit 1 (* rn we dont allow type annotations *)
  | Ast2.Let { name; value } ->
      typify value >>= fun value ->
      insert (name, type_of value) >>= fun _ -> return value

let typify exp context = typify exp (context, 0)

type constraints = (ty * ty) list

let rec generate_constraints expr =
  match expr with
  | Int _ | Float _ | String _ | Unit _ | Ident _ -> []
  | Application { func; arguement; ty } ->
      [ (type_of func, TFunction (type_of arguement, ty)) ]
      @ generate_constraints func
      @ generate_constraints arguement
  | If { condition; consequent; alternative; ty } ->
      [
        (type_of condition, TBool);
        (type_of consequent, ty);
        (type_of consequent, type_of alternative);
      ]
      @ generate_constraints condition
      @ generate_constraints consequent
      @ generate_constraints alternative
  | Function { parameter = { ty = p_ty; _ }; ty; abstraction } ->
      [ (ty, TFunction (p_ty, type_of abstraction)) ]
      @ generate_constraints abstraction
  | InfixApplication { ty; arguements = e1, e2; infix = { ty = f_ty; _ } } ->
      [ (f_ty, TFunction (type_of e1, TFunction (type_of e2, ty))) ]
      @ generate_constraints e1 @ generate_constraints e2
  | Let { value; _ } -> generate_constraints value

let print_constraints constraints =
  List.fold_left
    (fun first (c1, c2) ->
      first ^ "\n" ^ type_to_string c1 ^ " = " ^ type_to_string c2)
    "" constraints
