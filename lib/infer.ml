open Expr
open Monads.Std

let ( << ) f g x = f (g x)

module ST = struct
  module StateEnv = struct
    type t = string Seq.t
  end

  include Monad.State.T1 (StateEnv) (Monad.Ident)
  include Monad.State.Make (StateEnv) (Monad.Ident)
end

module R = struct
  module ReaderEnv = struct
    type t = (string * ty) list
  end

  module Reader = Monad.Reader.T1 (ReaderEnv) (ST)
  include Reader
  include Monad.Reader.Make (ReaderEnv) (ST)

  let _ = run

  let local f r =
    let f' e = run r (f e) |> lift in
    bind ~f:f' (read ())
end

module Err = struct
  type t = string
end

module ResultReader = Monad.Result.T1 (Err) (R)
module ResultReaderOps = Monad.Result.Make (Err) (R)
include ResultReader
include ResultReaderOps

let get x =
  let* env = lift (R.read ()) in
  Option.fold
    ~some:(fun x -> return x)
    ~none:("unbound variable " ^ x |> ResultReaderOps.fail)
    (env
    |> Stdlib.List.find_map (fun ((name : string), ty) ->
           if name = x then Some ty else None))

let chars = Stdlib.Seq.init 26 (fun x -> 97 + x |> Char.chr |> String.make 1)

let rec replicate n seq =
  let open Stdlib in
  if n = 0 then Seq.return ""
  else
    Seq.flat_map
      (fun res ->
        Seq.flat_map
          (fun rest -> res ^ rest |> Seq.return)
          (replicate (n - 1) seq))
      seq

let letters =
  let open Stdlib in
  Seq.ints 1 |> Seq.flat_map (fun x -> replicate x chars)

let new_meta =
  let* letters = ST.get () |> R.lift |> lift in
  let* letter, letters' =
    Stdlib.Option.fold
      ~none:(fail "ran out of fresh type variables")
      ~some:(fun (letter, letters') -> (TMeta letter, letters') |> return)
      (Stdlib.Seq.uncons letters)
  in
  let* _ = ST.put letters' |> R.lift |> lift in
  return letter

let in_env (name, ty) m =
  let scope env = (name, ty) :: env in
  let r = R.local scope m in
  r

(*let scoped_do f =*)
(*  (let open R in*)
(*   let* env = R.read () in*)
(*f env)*)
(*|> lift*)

(*let env_modify f =*)
(*  (let open R in*)
(*   let* env, s = ST.read () in*)
(*   let env' = (f env, s) in*)
(*   put env')*)
(*  |> lift*)

(*let update_env env =*)
(*  let open R in*)
(*  let* _, s = get () in*)
(*  put (env, s)*)

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

module SubstitableExpr : Substitable with type t = texpr = struct
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
        TPoly (metas, apply subst' expr)

  let ftv expr = type_of expr |> SubstitableType.ftv
end

let occurs_check a t = SubstitableType.ftv t |> MetaVariables.mem a
let compose s1 s2 = Subst.union (fun _ fst _ -> Some fst) s1 s2

let rec unify t1 t2 =
  match (t1, t2) with
  | _, _ when t1 = t2 -> return Subst.empty
  | TMeta t, ty when occurs_check t ty -> fail ""
  | ty, TMeta t when occurs_check t ty -> fail ""
  | TMeta t, ty | ty, TMeta t -> Subst.singleton t ty |> return
  | TArrow (t1, t2), TArrow (t1', t2') ->
      let* subs = unify t1 t1' in
      let* subs' =
        unify (SubstitableType.apply subs t2) (SubstitableType.apply subs t2')
      in
      compose subs subs' |> return
  | _ -> fail "unification error"

let generalize ty =
  let ty_ftv = SubstitableType.ftv ty in
  let get_env = R.read () |> lift in
  let* env = get_env in
  let env_ftv = SubstitableTypeEnv.ftv env in
  MetaVariables.diff ty_ftv env_ftv |> return

let instantiate : ty -> ty ResultReader.t = function
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

let infer expr =
  let rec infer_inner expr =
    match expr with
    | Var x ->
        x |> get
        |> bind ~f:(fun ty ->
               let* ty' = instantiate ty in
               return (Subst.empty, ty', TVar (x, ty')))
    | Lambda ((var : string), abs) ->
        let* arg_ty = new_meta in
        let* subs, abs_ty, abs' = in_env (var, arg_ty) (infer_inner abs) in
        let arg_ty' = SubstitableType.apply subs arg_ty in
        let ty = TArrow (arg_ty', abs_ty) in
        return (subs, ty, TLambda (var, arg_ty', abs', ty))
    | Application (abs, arg) ->
        let* subs, abs_ty, abs' = infer_inner abs in
        R.local
          (SubstitableTypeEnv.apply subs)
          (let* subs', arg_ty, arg' = infer_inner arg and* meta = new_meta in
           let abs_ty' = SubstitableType.apply subs' abs_ty in
           let* v = unify abs_ty' (TArrow (arg_ty, meta)) in
           let meta' = SubstitableType.apply v arg_ty in
           let subs''' = (compose subs << compose subs') v in
           return (subs''', meta', TApplication (abs', arg', meta')))
    | Let (var, e1, e2) ->
        let* subs, e1_ty, e1' = infer_inner e1 in
        R.local
          (SubstitableTypeEnv.apply subs)
          (let* free_variables = e1_ty |> generalize in

           let* subs', e2_ty, e2' =
             in_env (var, TPoly (free_variables, e1_ty)) (infer_inner e2)
           in
           let subs'' = compose subs subs' in
           return
             (subs'', e2_ty, TLet (var, TPoly (free_variables, e1'), e2', e2_ty)))
    | Boolean b -> return (Subst.empty, TBool, TBoolean (b, TBool))
    | Number n -> return (Subst.empty, TInt, TNumber (n, TInt))
    | If (cond, cons, alt) ->
        let* subs, cond_ty, cond' = infer_inner cond in
        let* subs', cons_ty, cons' = infer_inner cons in
        let* subs'', alt_ty, alt' = infer_inner alt in
        let* v = unify cond_ty TBool in
        let cons_ty' = SubstitableType.apply (compose subs v) cons_ty in
        let alt_ty' = SubstitableType.apply (compose subs v) alt_ty in
        let* v' = unify cons_ty' alt_ty' in
        let cons_ty'' = SubstitableType.apply v' cons_ty' in
        let subs''' =
          (compose subs << compose subs' << compose subs'' << compose v) v'
        in
        return (subs''', cons_ty', TIf (cond', cons', alt', cons_ty''))
  in
  let* subs, ty, expr' = infer_inner expr in
  (SubstitableExpr.apply subs expr', ty) |> return

let infer_many = List.map ~f:(map ~f:fst << infer)
let run e env = (run e |> R.run) env |> ST.run
let run_with_default e : ('a, string) result = run e [] letters |> fst

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
