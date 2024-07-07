open Expr
open Monads.Std

let ( << ) f g x = f (g x)

module ST = struct
  module Env = struct
    type t = (string * ty) list * int
  end

  include Monad.State.T1 (Env) (Monad.Ident)
  include Monad.State.Make (Env) (Monad.Ident)
end

module Err = struct
  type t = string
end

module ResultState = Monad.Result.T1 (Err) (ST)
module ResultStateOps = Monad.Result.Make (Err) (ST)
include ResultState
include ResultStateOps

let get x =
  let* env, _ = lift (ST.get ()) in
  Option.fold
    ~some:(fun x -> return x)
    ~none:(ResultStateOps.fail "unbound variable")
    (env
    |> Stdlib.List.find_map (fun ((name : string), ty) ->
           if name == x then Some ty else None))

let new_meta =
  ST.get ()
  |> ST.map ~f:(fun (_, meta) -> TMeta (meta |> string_of_int))
  |> lift

let scoped_do f =
  let open ST in
  let* env, _ = ST.get () in
  let* r = f env and* _, s = ST.get () in
  let* _ = ST.put (env, s) in
  return r

let update_env env =
  let open ST in
  let* _, s = get () in
  put (env, s)

module Subst = Map.Make (String)

type subst = ty Subst.t

module type Substitable = sig
  type t

  val apply : subst -> t -> t
  val ftv : t -> MetaVariables.t
end

module SubstitableType : Substitable with type t = ty = struct
  type t = ty

  let rec apply subst = function
    | (TBool | TInt) as ty -> ty
    | TMeta meta as ty ->
        Subst.find_opt meta subst |> Option.fold ~none:ty ~some:(fun x -> x)
    | TArrow (t1, t2) -> TArrow (apply subst t1, apply subst t2)
    | TPoly (metas, ty) ->
        (*TODO: foldr*)
        let subst' = MetaVariables.fold Subst.remove metas subst in
        TPoly (metas, apply subst' ty)

  let rec ftv = function
    | TBool | TInt -> MetaVariables.empty
    | TMeta meta -> MetaVariables.singleton meta
    | TArrow (t1, t2) -> MetaVariables.union (ftv t1) (ftv t2)
    | TPoly (metas, ty) -> MetaVariables.diff (ftv ty) metas
end

module SubstitableA (S : Substitable) : Substitable with type t = S.t list =
struct
  type t = S.t list

  let apply = Stdlib.List.map << S.apply

  let ftv this =
    Stdlib.List.fold_right
      (MetaVariables.union << S.ftv)
      this MetaVariables.empty
end

module SubstitableTypeEnv : Substitable with type t = (string * ty) list =
struct
  type t = (string * ty) list

  module SubstitableTypes = SubstitableA (SubstitableType)

  let apply s env =
    Stdlib.List.map (fun (name, ty) -> (name, SubstitableType.apply s ty)) env

  let ftv env = Stdlib.List.map (fun (_, ty) -> ty) env |> SubstitableTypes.ftv
end

module SubstitableExpr : Substitable = struct
  type t = texpr

  (*apply is rescursive so that all types are filled in in all sub expressions*)
  let rec apply subs = function
    | TVar (var, ty) -> TVar (var, SubstitableType.apply subs ty)
    | (TBoolean _ | TNumber _) as e -> e
    | TIf (cond, cons, alt, ty) ->
        TIf
          ( apply subs cond,
            apply subs cons,
            apply subs alt,
            SubstitableType.apply subs ty )
    | TLet (var, e1, e2, ty) ->
        TLet (var, apply subs e1, apply subs e2, SubstitableType.apply subs ty)
    | TLambda (var, arg_ty, abs, ty) ->
        TLambda
          ( var,
            SubstitableType.apply subs arg_ty,
            apply subs abs,
            SubstitableType.apply subs ty )
    | TApplication (abs, arg, ty) ->
        TApplication
          (apply subs abs, apply subs arg, SubstitableType.apply subs ty)
    | TPoly (metas, expr) ->
        let subst' = MetaVariables.fold Subst.remove metas subs in
        apply subst' expr

  let ftv expr = type_of expr |> SubstitableType.ftv
end

let occurs_check a t = SubstitableType.ftv t |> MetaVariables.mem a

let rec unify t1 t2 subs =
  match (t1, t2) with
  | _, _ when t1 = t2 -> return subs
  | TMeta t, ty when occurs_check t ty -> fail ""
  | ty, TMeta t when occurs_check t ty -> fail ""
  | TMeta t, ty | ty, TMeta t ->
      Subst.union (fun _ fst _ -> Some fst) (Subst.singleton t ty) subs
      |> return
  | TArrow (t1, t2), TArrow (t1', t2') ->
      let* subs' = unify t1 t1' subs in
      unify t2 t2' subs'
  | _ -> fail "unification error"

let generalize subs ty =
  let ty' = SubstitableType.apply subs ty in
  let ty_ftv = SubstitableType.ftv ty' in
  let get_env = ST.gets fst |> lift in
  let* env = get_env in
  let env' = SubstitableTypeEnv.apply subs env in
  let env_ftv = SubstitableTypeEnv.ftv env' in
  MetaVariables.diff ty_ftv env_ftv |> return

let instantiate : ty -> ty ResultState.t = function
  | TPoly (metas, ty) ->
      let* subs =
        MetaVariables.to_seq metas |> Stdlib.List.of_seq
        |> List.map ~f:(fun meta ->
               let* ty = new_meta in
               return (meta, ty))
      in
      let subs' = subs |> Stdlib.List.to_seq |> Subst.of_seq in

      SubstitableType.apply subs' ty |> return
  | ty -> return ty

let rec infer subs expr =
  match expr with
  | Var x ->
      x |> get
      |> bind ~f:(fun ty ->
             let* ty' = instantiate ty in
             return (subs, TVar (x, ty')))
  | Boolean b -> return (subs, TBoolean (b, TBool))
  | Number n -> return (subs, TNumber (n, TInt))
  | If (cond, cons, alt) ->
      let* subs', cond' = infer subs cond in
      let* subs'', cons' = infer subs' cons in
      let* subs''', alt' = infer subs'' alt in
      let* v = unify (type_of cond') TBool subs''' in
      let* v' = unify (type_of cons') (type_of alt') v in
      return (v', TIf (cond', cons', alt', type_of cons'))
  | Let (var, e1, e2) ->
      let* subs', e1' = infer subs e1 in
      let* free_variables = type_of e1' |> generalize subs' in

      let* subs'', e2' =
        scoped_do (fun env ->
            let* _ =
              let new_binding : string * ty =
                (var, TPoly (free_variables, type_of e1'))
              in
              new_binding :: env |> update_env |> return
            in
            infer subs e2)
      in
      return (subs'', TLet (var, TPoly (free_variables, e1'), e2', type_of e2'))
  | Lambda ((var : string), abs) ->
      let* arg_ty = new_meta in
      let* subs', abs' =
        scoped_do (fun env ->
            let* _ = (var, arg_ty) :: env |> update_env |> return in
            infer subs abs)
      in
      return (subs', TLambda (var, arg_ty, abs', TArrow (arg_ty, type_of abs')))
  | Application (abs, arg) ->
      let* subs', abs' = infer subs abs in
      let* subs'', arg' = infer subs' arg and* meta = new_meta in
      let* v = unify (type_of abs') (TArrow (type_of arg', meta)) subs'' in
      return (v, TApplication (abs', arg', meta))

let rec generate_constraints expr =
  match expr with
  | TVar _ | TNumber _ | TBoolean _ -> []
  | TIf (cond, cons, alt, ty) ->
      (type_of cond, TBool)
      :: (type_of cons, ty)
      :: (type_of alt, ty)
      :: generate_constraints cond
      @ generate_constraints cons @ generate_constraints alt
  | TLet (_, e1, e2, ty) ->
      (*TODO: constrain var's type?*)
      ((type_of e2, ty) :: generate_constraints e1) @ generate_constraints e2
  | TLambda (_, arg_ty, abs, ty) ->
      (TArrow (arg_ty, type_of abs), ty) :: generate_constraints abs
  | TApplication (abs, arg, ty) ->
      ((type_of abs, TArrow (type_of arg, ty)) :: generate_constraints abs)
      @ generate_constraints arg
  | TPoly (_, e) -> generate_constraints e
