open Typed_ast
open Types
module MetaS = Set.Make (Int)

let ( >>= ) (t : 's * 'm -> ('a * ('s * 'm), string) result)
    (f : 'a -> 's * 'm -> ('b * ('s * 'm), string) result) (s : 's * 'm) :
    ('b * ('s * 'm), string) result =
  Result.bind (t s) (fun (a, s') -> f a s')

let return a (s, m) = Ok (a, (s, m))
let zero a _ = Error a

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

module IntMap = Map.Make (Int)

let rec instantiate ty (tmap : ty IntMap.t) =
  match ty with
  | TPoly (ms, t) ->
      List.fold_left
        (fun ms' n ->
          ms' >>= fun ms' ->
          new_meta <$> fun nm -> IntMap.add n nm ms')
        (return tmap) ms
      >>= fun ms' -> instantiate t ms'
  | Meta m -> return (Option.value (IntMap.find_opt m tmap) ~default:ty)
  | TFunction (t1, t2) ->
      instantiate t1 tmap >>= fun t1' ->
      instantiate t2 tmap <$> fun t2' -> TFunction (t1', t2')
  | _ -> return ty

(* let typify exp context = typify exp (context, 0) *)

(* TODO: might need constarints besides for type equaility (more like subtyping) for infering tuple and record projections *)
type constraints = (ty * ty) list

let todo string =
  print_endline string;
  exit 1

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
  | Let { e1; e2; _ } -> generate_constraints e1 @ generate_constraints e2
  | Rec { expr; _ } -> generate_constraints expr
  | Poly { e; _ } -> generate_constraints e (* | e -> *)
  | Record _r -> todo "generate constraints for record"
  | TupleAcces { ty = _ty; value = _value; _ } ->
      todo "generate constraints for tuple access"
  | RecordAcces _ra -> todo "generate constraints for record access"
  | Constructor _c -> todo "generate constraints for variant constructors"
  | Tuple t ->
      (t.ty, TTuple (List.map type_of t.pair))
      :: List.concat_map generate_constraints t.pair

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
            ("could not unify " ^ type_to_string t1 ^ " and "
           ^ type_to_string t2))

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
  | Rec { name; expr; _ } -> Rec { name; expr = substitute expr; ty }
  | Let { name; e1; e2; _ } ->
      Let { name; e1 = substitute e1; e2 = substitute e2; ty }
  (* TODO: subsitite non polymorphic type variables in poly *)
  | _ -> expr

let rec metas ty =
  match ty with
  | Meta m -> MetaS.singleton m
  | TFunction (t1, t2) -> metas t2 |> (metas t1 |> MetaS.union)
  | _ -> MetaS.empty

let find_free ms ty =
  let ms' = metas ty in
  MetaS.diff ms ms'

let rec find_free_in_env ms env =
  if MetaS.is_empty ms then ms
  else
    match env with
    | [] -> ms
    | (_, ty) :: env' ->
        let ms' = find_free ms ty in
        find_free_in_env ms' env'

let generalize expr s =
  Result.map
    (fun subs ->
      let exp = substitute subs expr in
      let fv = find_free_in_env (type_of exp |> metas) (fst s) in
      (Poly { e = exp; metas = MetaS.to_list fv }, s))
    (unify (generate_constraints expr))

let rec_no_func expr =
  match expr with
  | Ast2.Function _ -> return expr
  | _ ->
      "expression " ^ Ast2.ast_to_string expr
      ^ " is invalid on left hand side of let rec"
      |> zero

let rec typify expr =
  match expr with
  | Ast2.Int i -> return (Int { ty = TInteger; value = i })
  | Ast2.Float i -> return (Float { ty = TFloat; value = i })
  | Ast2.String i -> return (String { ty = TString; value = i })
  | Ast2.Ident i ->
      get i >>= fun ty ->
      instantiate ty IntMap.empty <$> fun ty' -> Ident { ty = ty'; ident = i }
      (* TODO: make ident type be adt of unit, wildcard or string if paramater = some unit insert follow parameter = non case *)
  | Ast2.Function { parameter = Some { ident; ty = ty_opt }; abstraction } ->
      new_meta >>= fun f_ty ->
      (match ty_opt with None -> new_meta | Some ty -> return ty)
      >>= fun a_ty ->
      scoped_insert (ident, a_ty) (fun () ->
          typify abstraction >>= fun abstraction ->
          return
            (Function
               { abstraction; parameter = { ident; ty = a_ty }; ty = f_ty }))
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
      generalize e1 >>= fun e1 ->
      scoped_insert (name, type_of e1) (fun () -> typify e2) >>= fun e2 ->
      return (Let { name; ty = type_of e2; e1; e2 })
  | Ast2.LetRec { e1; e2; name } ->
      rec_no_func e1 >>= fun e1 ->
      new_meta >>= fun e1_ty ->
      scoped_insert (name, e1_ty) (fun () -> typify e1) >>= fun e1 ->
      generalize e1 >>= fun e1 ->
      scoped_insert (name, type_of e1) (fun () -> typify e2) >>= fun e2 ->
      return
        (Let
           {
             name;
             ty = type_of e2;
             e1 = Rec { ty = type_of e1; expr = e1; name };
             e2;
           })
  | Ast2.Tuple tuple ->
      new_meta >>= fun ty ->
      List.fold_right
        (fun expr tuple ->
          typify expr >>= fun expr' ->
          tuple <$> fun tuple' -> expr' :: tuple')
        tuple (return [])
      <$> fun pair -> Tuple { pair; ty }
  | Ast2.Record record ->
      new_meta >>= fun ty ->
      List.fold_left
        (fun tuple (expr : Ast2.ast2 Ast.field) ->
          typify expr.value >>= fun expr' ->
          tuple <$> fun tuple' -> { value = expr'; name = expr.name } :: tuple')
        (return []) record
      <$> fun fields -> Record { fields; ty }
  | Ast2.Constructor { name; value } ->
      new_meta >>= fun ty ->
      typify value <$> fun value -> Constructor { name; value; ty }
  | Ast2.RecordAcces { projector; value } ->
      new_meta >>= fun ty ->
      typify value <$> fun value -> RecordAcces { projector; value; ty }
  | Ast2.TupleAcces { projector; value } ->
      new_meta >>= fun ty ->
      typify value <$> fun value -> TupleAcces { projector; value; ty }

let infer expr =
  typify expr >>= fun typed_expr s ->
  let constraints = generate_constraints typed_expr in
  Result.map
    (fun substitutions -> (substitute substitutions typed_expr, s))
    (unify constraints)

let inspect (s, m) =
  String.concat "," (List.map (fun (b, ty) -> b ^ ":" ^ type_to_string ty) s)
  |> print_endline;
  return () (s, m)

let infer tl =
  match tl with
  | Ast2.RecBind { name; value } ->
      rec_no_func value >>= fun value ->
      (* TODO: make ident type be adt of unit, wildcard or string if unit insert (name, unit) *)
      new_meta >>= fun value_ty ->
      scoped_insert (name, value_ty) (fun () -> infer value) >>= fun value' ->
      generalize value' >>= fun value' ->
      insert (name, type_of value') >>= fun () ->
      return
        (Bind
           {
             name;
             value = Rec { expr = value'; ty = type_of value'; name };
             ty = type_of value';
           })
  | Ast2.TypeBind { name; ty } -> TypeBind { name; ty } |> return
  | Ast2.Bind { name; value } ->
      (* TODO: make ident type be adt of unit, wildcard or string if unit insert (name, unit) *)
      infer value >>= fun value' ->
      generalize value' >>= fun value' ->
      insert (name, type_of value') >>= fun () ->
      return (Bind { name; value = value'; ty = type_of value' })
  | Ast2.PrintString s -> return (PrintString s)

(* TODO: static envoirment *)
let infer tls =
  List.fold_left
    (fun i tl ->
      i >>= fun tls ->
      infer tl >>= fun tl' -> return (tls @ [ tl' ]))
    (return []) tls
    ( [
        ("print", TPoly ([ 1 ], TFunction (Meta 1, TUnit)));
        ("=", TPoly ([ 1 ], TFunction (Meta 1, TFunction (Meta 1, TBool))));
        ("-", TFunction (TInteger, TFunction (TInteger, TInteger)));
        ("*", TFunction (TInteger, TFunction (TInteger, TInteger)));
      ],
      0 )

let print_constraints constraints =
  List.fold_left
    (fun first (c1, c2) ->
      first ^ "\n" ^ type_to_string c1 ^ " = " ^ type_to_string c2)
    "" constraints
