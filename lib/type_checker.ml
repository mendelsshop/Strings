open Typed_ast
module MetaS = Set.Make (Int)

let ( >>= ) (t : 's * 'm -> ('a * ('s * 'm), string) result)
    (f : 'a -> 's * 'm -> ('b * ('s * 'm), string) result) (s : 's * 'm) :
    ('b * ('s * 'm), string) result =
  Result.bind (t s) (fun (a, s') -> f a s')

let return a (s, m) = Ok (a, (s, m))

let ( <$> ) (t : 's * 'm -> ('a * ('s * 'm), string) result) (f : 'a -> 'b)
    (s : 's * 'm) : ('b * ('s * 'm), string) result =
  Result.map (fun (a, s') -> (f a, s')) (t s)

let new_meta (s, m) = Ok (Meta m, (s, m + 1))
let insert e (s, m) = Ok ((), (e :: s, m))
let remove_fst (s, m) = Ok ((), match s with [] -> (s, m) | _ :: s' -> (s', m))

(* scoped insert allows temporary insertion, but the meta variable created are not temporary *)
let scoped_insert e f (s, m) =
  Result.map
    (fun (e', (_, m')) -> (e', (s, m')))
    (((fun (s, m) -> Ok ((), (e :: s, m))) >>= fun _ -> f ()) (s, m))

let get v (s, m) =
  Result.map
    (fun r -> (r, (s, m)))
    (List.assoc_opt v s |> Option.to_result ~none:("unbound variable " ^ v))

(* let typify exp context = typify exp (context, 0) *)
let rec typify expr =
  match expr with
  | Ast2.Int i -> return (Int { ty = TInteger; value = i })
  | Ast2.Float i -> return (Float { ty = TFloat; value = i })
  | Ast2.String i -> return (String { ty = TString; value = i })
  | Ast2.Ident i ->
      get i >>= fun ty -> return (Ident { ty; ident = i })
      (* TODO: make ident type be adt of unit, wildcard or string if paramater = some unit insert follow parameter = non case *)
  | Ast2.Function { parameter = Some ident; abstraction } ->
      new_meta >>= fun m ->
      new_meta >>= fun a_ty ->
      scoped_insert (ident, m) (fun () ->
          typify abstraction >>= fun abstraction ->
          return
            (Function { abstraction; parameter = { ident; ty = m }; ty = a_ty }))
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
  | Ast2.Let { e1; e2; name } ->
      typify e1 >>= fun e1 ->
      scoped_insert (name, type_of e1) (fun () -> typify e2) >>= fun e2 ->
      return (Let { name; ty = type_of e2; e1; e2 })

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
        (ty, type_of consequent);
        (ty, type_of alternative);
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
  | Let _ ->
      print_endline "let polymorphism not supported yet";
      exit 1

let rec mini_sub (m, s_ty) ty =
  match ty with
  | TFunction (t1, t2) ->
      TFunction (mini_sub (m, s_ty) t1, mini_sub (m, s_ty) t2)
  | Meta n when m = n -> s_ty
  | _ -> ty

let rec unify constraints =
  match constraints with
  | [] -> Ok []
  | (t1, t2) :: constraints -> (
      match (t1, t2) with
      | t1, t2 when t1 = t2 -> unify constraints
      | TFunction (t1, t2), TFunction (t3, t4) ->
          unify ((t1, t3) :: (t2, t4) :: constraints)
      | Meta m, t | t, Meta m ->
          Result.map
            (fun subs -> (m, t) :: subs)
            (unify
               (List.map
                  (fun (t1, t2) -> (mini_sub (m, t) t1, mini_sub (m, t) t2))
                  constraints))
      | t1, t2 ->
          Error
            ("could not unify" ^ type_to_string t1 ^ " and " ^ type_to_string t2)
      )

let rec subs substitutions ty =
  match substitutions with
  | [] -> ty
  | sub :: substitutions -> subs substitutions (mini_sub sub ty)

let rec substitute substitutions expr =
  let substitute = substitute substitutions in
  let ty = subs substitutions (type_of expr) in
  match expr with
  | Function { parameter = { ident; ty = p_ty }; abstraction; _ } ->
      Function
        {
          parameter = { ident; ty = subs substitutions p_ty };
          abstraction = substitute abstraction;
          ty;
        }
  | Ident { ident; _ } -> Ident { ident; ty }
  | If { condition; consequent; alternative; _ } ->
      If
        {
          condition = substitute condition;
          consequent = substitute consequent;
          alternative = substitute alternative;
          ty;
        }
  | Application { func; arguement; _ } ->
      Application
        { func = substitute func; arguement = substitute arguement; ty }
  | InfixApplication { infix = { ident; ty = i_ty }; arguements = e1, e2; _ } ->
      InfixApplication
        {
          infix = { ident; ty = subs substitutions i_ty };
          arguements = (substitute e1, substitute e2);
          ty;
        }
  | Let _ ->
      print_endline "let polymorphism not supported yet";
      exit 1
  | _ -> expr

let infer expr =
  typify expr >>= fun typed_expr s ->
  let constraints = generate_constraints typed_expr in
  Result.map
    (fun substitutions -> (substitute substitutions typed_expr, s))
    (unify constraints)

let infer tl =
  match tl with
  | Ast2.Bind { name; value } ->
      (* TODO: make ident type be adt of unit, wildcard or string if unit insert (name, unit) *)
      infer value >>= fun value' ->
      insert (name, type_of value') >>= fun () ->
      return (Bind { name; value = value'; ty = type_of value' })
  | Ast2.PrintString s -> return (PrintString s)

(* TODO: static envoirment *)
let infer tls =
  List.fold_left
    (fun i tl ->
      i >>= fun tls ->
      infer tl >>= fun tl' -> return (tls @ [ tl' ]))
    (return []) tls ([], 0)

let print_constraints constraints =
  List.fold_left
    (fun first (c1, c2) ->
      first ^ "\n" ^ type_to_string c1 ^ " = " ^ type_to_string c2)
    "" constraints
