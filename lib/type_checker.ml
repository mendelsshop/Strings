open Typed_ast
open Types
module MetaS = Set.Make (Int)

let ( >>= )
    (t :
      (string * ty) list * int * (string * ty) list ->
      ('a * ((string * ty) list * int * (string * ty) list), string) result)
    (f :
      'a ->
      (string * ty) list * int * (string * ty) list ->
      ('b * ((string * ty) list * int * (string * ty) list), string) result)
    (s : (string * ty) list * int * (string * ty) list) :
    ('b * ((string * ty) list * int * (string * ty) list), string) result =
  Result.bind (t s) (fun (a, s') -> f a s')

let return a (s, m, t) = Ok (a, (s, m, t))
let zero a _ = Error a

let ( <$> )
    (t :
      (string * ty) list * int * (string * ty) list ->
      ('a * ((string * ty) list * int * (string * ty) list), string) result)
    (f : 'a -> 'b) (s : (string * ty) list * int * (string * ty) list) :
    ('b * ((string * ty) list * int * (string * ty) list), string) result =
  Result.map (fun (a, s') -> (f a, s')) (t s)

let new_meta (s, m, t) = return (Meta m) (s, m + 1, t)
let insert e (s, m, t) = return () (e :: s, m, t)
let insert_type e (s, m, t) = return () (s, m, e :: t)

let remove_fst (s, m, t) =
  return () (match s with [] -> (s, m, t) | _ :: s' -> (s', m, t))

(* scoped insert allows temporary insertion, but the meta variable created are not temporary *)
let scoped_insert e f (s, m, t) =
  Result.map
    (fun (e', (_, m', _)) -> (e', (s, m', t)))
    (((fun (s, m, t) -> Ok ((), (e :: s, m, t))) >>= fun _ -> f ()) (s, m, t))

let get v (s, m, t) =
  Result.map
    (fun r -> (r, (s, m, t)))
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
  | TRecord t -> instantiate t tmap <$> fun t' -> TRecord t'
  | TRowExtension { field; row_extension; label } ->
      instantiate field tmap >>= fun field' ->
      instantiate row_extension tmap <$> fun row_extension' ->
      TRowExtension { row_extension = row_extension'; label; field = field' }
  | _ -> return ty

(* let typify exp context = typify exp (context, 0) *)

(* TODO: might need constarints besides for type equaility (more like subtyping) for infering tuple and record projections *)
type constraints = (ty * ty) list

let todo string =
  print_endline string;
  exit 1

module ConstraintGenerator : sig
  val generate_constraints : typed_ast -> int -> (ty * ty) list * int
end = struct
  let return e meta = (e, meta)

  let map t f m =
    let e, m' = t m in
    (f e, m')

  let bind t f m =
    let e, m' = t m in
    f e m'

  let ( >>= ) = bind
  let ( <$> ) = map

  let ( @ ) a b =
    a >>= fun constraints_a ->
    b <$> fun constraints_b -> constraints_a @ constraints_b

  (* cons operator *)
  let ( ++ ) a b =
    a >>= fun constraint_a ->
    b <$> fun constraints_b -> constraint_a :: constraints_b

  let new_meta m = return (Meta m) (m + 1)

  let rec generate_constraints expr =
    match expr with
    | Int _ | Float _ | String _ | Unit _ | Ident _ -> return []
    | Application { func; arguement; ty } ->
        return (type_of func, TFunction (type_of arguement, ty))
        ++ generate_constraints func
        @ generate_constraints arguement
    | If { condition; consequent; alternative; ty } ->
        return
          [
            (type_of condition, TBool);
            (ty, type_of consequent);
            (ty, type_of alternative);
          ]
        @ generate_constraints condition
        @ generate_constraints consequent
        @ generate_constraints alternative
    | Function { parameter = { ty = p_ty; _ }; ty; abstraction } ->
        return (ty, TFunction (p_ty, type_of abstraction))
        ++ generate_constraints abstraction
    | Let { e1; e2; _ } -> generate_constraints e1 @ generate_constraints e2
    | Rec { expr; _ } -> generate_constraints expr
    | Poly { e; _ } -> generate_constraints e (* | e -> *)
    | Record { fields; ty } ->
        return
          ( ty,
            TRecord
              (List.fold_left
                 (fun row (field : typed_ast field) ->
                   TRowExtension
                     {
                       label = field.name;
                       field = type_of field.value;
                       row_extension = row;
                     })
                 TEmptyRow fields) )
        ++ (fields
           |> List.map (fun (field : typed_ast field) -> field.value)
           |> List.map generate_constraints
           |> List.fold_left
                (fun tys ty ->
                  tys >>= fun tys' ->
                  ty <$> fun ty' -> List.append ty' tys')
                (return []))
    | TupleAcces { ty = _ty; value = _value; _ } ->
        todo "generate constraints for tuple access"
    | RecordAcces { value; ty; projector } ->
        ( new_meta <$> fun rest_row ->
          ( TRecord
              (TRowExtension
                 { label = projector; field = ty; row_extension = rest_row }),
            type_of value ) )
        ++ generate_constraints value
    | Constructor _c -> todo "generate constraints for variant constructors"
    | Tuple t ->
        return (t.ty, TTuple (List.map type_of t.pair))
        ++ (t.pair
           |> List.map generate_constraints
           |> List.fold_left
                (fun tys ty ->
                  tys >>= fun tys' ->
                  ty <$> fun ty' -> List.append ty' tys')
                (return []))
end

let rec mini_sub (m, s_ty) ty =
  match ty with
  | TFunction (t1, t2) ->
      TFunction (mini_sub (m, s_ty) t1, mini_sub (m, s_ty) t2)
  | Meta n when m = n -> s_ty
  | TRecord t -> TRecord (mini_sub (m, s_ty) t)
  | TRowExtension { label; field; row_extension } ->
      TRowExtension
        {
          label;
          field = mini_sub (m, s_ty) field;
          row_extension = mini_sub (m, s_ty) row_extension;
        }
  | _ -> ty

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
  | RecordAcces { projector; value; _ } ->
      RecordAcces { projector; value = substitute value; ty }
  | Record { fields; _ } ->
      Record
        {
          fields =
            List.map
              (fun field ->
                { name = field.name; value = substitute field.value })
              fields;
          ty;
        }
  (* TODO: subsitite non polymorphic type variables in poly *)
  | _ -> expr

let rec metas ty =
  match ty with
  | Meta m -> MetaS.singleton m
  | TFunction (t1, t2) -> metas t2 |> (metas t1 |> MetaS.union)
  | TRecord t -> metas t
  | TRowExtension { field; row_extension; _ } ->
      metas field |> (metas row_extension |> MetaS.union)
  | _ -> MetaS.empty

let find_free ms ty =
  let ms' = metas ty in
  MetaS.diff ms ms'

module Unifier : sig
  val unify : (ty * ty) list -> int -> ((int * ty) list * int, string) result
end = struct
  let return e meta = Ok (e, meta)
  let map t f m = Result.map (fun (e, m') -> (f e, m')) (t m)
  let bind t f m = Result.bind (t m) (fun (e, m') -> f e m')
  let zero e _ = Error e
  let ( >>= ) = bind
  let ( <$> ) = map

  let ( @ ) a b =
    a >>= fun sub_a ->
    b <$> fun sub_b -> sub_a @ sub_b

  let new_meta m = return (Meta m) (m + 1)

  (* cons operator *)
  let ( ++ ) a b = b <$> fun sub_b -> a :: sub_b

  let rec unify constraints =
    let rec row_rewrite l ty row =
      match row with
      | TEmptyRow -> "row does not contain label " ^ l |> zero
      | TRowExtension { field; label; row_extension } when label = l ->
          unify [ (ty, field) ] <$> fun subs -> (row_extension, subs)
      | TRowExtension { field; label; row_extension } ->
          row_rewrite l ty row_extension <$> fun (row', sub) ->
          (TRowExtension { label; field; row_extension = row' }, sub)
      | Meta m ->
          new_meta <$> fun row' ->
          ( row',
            [
              (m, TRowExtension { label = l; field = ty; row_extension = row' });
            ] )
      | _ ->
          "row type expected with label " ^ l ^ " ,but type "
          ^ type_to_string row ^ " was found"
          |> zero
    in

    match constraints with
    | [] -> return []
    | (t1, t2) :: constraints -> (
        match (t1, t2) with
        | t1, t2 when t1 = t2 -> unify constraints
        | TFunction (t1, t2), TFunction (t3, t4) ->
            (t1, t3) :: (t2, t4) :: constraints |> unify
        | Meta m, t | t, Meta m ->
            (m, t)
            ++ (constraints
               |> List.map (fun (t1, t2) ->
                      (mini_sub (m, t) t1, mini_sub (m, t) t2))
               |> unify)
            (* todo: better error for when two records don't unify - right now it gets down to empty row and errors with "not type checked: could not unify a int '7 and {}" *)
        | TRecord (TRowExtension _ as r1), TRecord (TRowExtension _ as r2) ->
            (r1, r2) :: constraints |> unify
            (* | ( TRowExtension { label = label1; field = ty1; row_extension = row1 }, *)
            (*     TRowExtension { label = label2; field = ty2; row_extension = row2 } *)
            (*   ) *)
            (*   when label1 = label2 -> *)
            (*     print_endline (type_to_string t1 ^ "~= " ^ type_to_string t2); *)
            (*     Result.bind *)
            (*       (unify [ (ty1, ty2) ]) *)
            (*       (fun sub1 -> *)
            (*         let row1, row2 = (subs sub1 row1, subs sub1 row2) in *)
            (*         Result.bind *)
            (*           (unify [ (row1, row2) ]) *)
            (*           (fun sub2 -> *)
            (*             if *)
            (*               MetaS.is_empty *)
            (*                 (find_free (sub1 |> List.map fst |> MetaS.of_list) row1) *)
            (*             then *)
            (*               Result.map *)
            (*                 (fun sub3 -> sub1 @ sub2 @ sub3) *)
            (*                 (unify constraints) *)
            (*             else Error "")) *)
            (* unify ((ty1, ty2) :: (row1, row2) :: constraints) *)
        | ( TRowExtension { label; field; row_extension = row1 },
            (TRowExtension _ as row2) ) ->
            (* TODO: make sure sub1's meta variables are not containted in row2 to ensure type infernce termination
               look at the commented out case above for how to do so
            *)
            ( row_rewrite label field row2 >>= fun (row2', sub1) ->
              unify [ (subs sub1 row1, subs sub1 row2') ] <$> fun sub2 ->
              List.append sub1 sub2 )
            @ unify constraints
        | t1, t2 ->
            "could not unify " ^ type_to_string t1 ^ " and " ^ type_to_string t2
            |> zero)
end

let rec find_free_in_env ms env =
  if MetaS.is_empty ms then ms
  else
    match env with
    | [] -> ms
    | (_, ty) :: env' ->
        let ms' = find_free ms ty in
        find_free_in_env ms' env'

let generalize expr (s : (string * ty) list * int * (string * ty) list) =
  let s, m, t = s in
  Result.map
    (fun (subs, m') ->
      let exp = substitute subs expr in
      let fv = find_free_in_env (type_of exp |> metas) s in
      (Poly { e = exp; metas = MetaS.to_list fv }, (s, m', t)))
    (let cs, m' = ConstraintGenerator.generate_constraints expr m in
     Result.map (fun (subs, m'') -> (subs, m'')) (Unifier.unify cs m'))

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
  | Ast2.Function { parameter = PIdent ident; abstraction } ->
      new_meta >>= fun f_ty ->
      new_meta >>= fun a_ty ->
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
  | Ast2.Function { parameter = PUnit; abstraction } ->
      typify abstraction >>= fun abstraction ->
      new_meta >>= fun a_ty ->
      return
        (Function
           {
             abstraction;
             parameter = { ident = "()"; ty = TUnit };
             ty = TFunction (TUnit, a_ty);
           })
  | Ast2.Let { e1; e2; name = PIdent name } ->
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
  | Ast2.Let { name = PUnit; e1; e2 } ->
      typify e1 >>= fun e1 ->
      generalize e1 >>= fun e1 ->
      typify e2 >>= fun e2 ->
      return (Let { name = "()"; ty = type_of e2; e1; e2 })
  | _ -> zero ("not supported yet " ^ Ast2.ast_to_string expr)

let infer expr =
  typify expr >>= fun typed_expr s ->
  let s, m, t = s in
  let constraints, m' = ConstraintGenerator.generate_constraints typed_expr m in
  Result.map
    (fun (substitutions, m'') ->
      (substitute substitutions typed_expr, (s, m'', t)))
    (Unifier.unify constraints m')

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
  | Ast2.TypeBind { name; ty } ->
      (* TODO: validate types *)
      (name, ty) |> insert_type <$> fun _ -> TypeBind { name; ty }
  | Ast2.Bind { name = PIdent name; value } ->
      (* TODO: make ident type be adt of unit, wildcard or string if unit insert (name, unit) *)
      infer value >>= fun value' ->
      generalize value' >>= fun value' ->
      insert (name, type_of value') >>= fun () ->
      return (Bind { name; value = value'; ty = type_of value' })
  | Ast2.Bind { name = PUnit; value } ->
      infer value >>= fun value' ->
      generalize value' >>= fun value' ->
      if type_of value' = TUnit then
        return (Bind { name = "()"; value = value'; ty = type_of value' })
      else
        ast_to_string value' ^ " does not have type unit, it has type "
        ^ (type_of value' |> type_to_string)
        |> zero
  | Ast2.PrintString s -> return (PrintString s)
  | _ -> "not supported yet: " ^ Ast2.print_top_level tl |> zero

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
      0,
      [] )

let print_constraints constraints =
  List.fold_left
    (fun first (c1, c2) ->
      first ^ "\n" ^ type_to_string c1 ^ " = " ^ type_to_string c2)
    "" constraints
