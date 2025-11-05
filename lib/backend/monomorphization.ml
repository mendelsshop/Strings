open Typed_ast
open Utils

(* TODO: issues
   how to monomorphize letrecs - (polymorphic recursion issues?) - fix each let(rec) whether at the top level or not will have multiple copies of the `let pat = expr`
   something like:
   type 't let  { name: tpattern; value; 't mexpr; ty: ty; span: span }  maybe do not need span
   type 't mexpr
   | MLet { lets: 't let; e2: 't mexpr; span: span; ty: ty }
   | MLetRec { lets: 't let; e2: 't mexpr; span: span; ty: ty }
   ...
   type 't top_levl
   | MBind { lets: 't let; e2: 't mexpr;  }
   | MRecBind { lets: 't let;  }
   ...
*)

module TypeEnv = Infer.SimpleTypeEnv

module Scheme = struct
  type t = TypeEnv.t ref
end

module SchemeEnv = Utils.Env.Make (Scheme)

type 't mexpr =
  | MVar of { ident : string; ty : 't; span : AMPCL.span }
  | MFloat of { value : float; ty : 't; span : AMPCL.span }
  | MString of { value : string; ty : 't; span : AMPCL.span }
  | MInteger of { value : int; ty : 't; span : AMPCL.span }
  | MBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | MLambda of {
      parameter : 't tpattern;
      parameter_ty : 't;
      body : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MApplication of {
      lambda : 't mexpr;
      arguement : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MUnit of { ty : 't; span : AMPCL.span }
  (* the instantiations are for all variables bound by the let *)
  | MLet of {
      instantiations : SchemeEnv.t;
      name : 't tpattern;
      name_ty : 't;
      e1 : 't mexpr;
      e2 : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MLetRec of {
      instantiations : SchemeEnv.t;
      name : 't tpattern;
      name_ty : 't;
      e1 : 't mexpr;
      e2 : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MIf of {
      condition : 't mexpr;
      consequent : 't mexpr;
      alternative : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MRecordAccess of {
      record : 't mexpr;
      projector : string;
      ty : 't;
      span : AMPCL.span;
    }
  | MRecordExtend of {
      record : 't mexpr;
      new_fields : 't mexpr row;
      ty : 't;
      span : AMPCL.span;
    }
  | MRecord of { fields : 't mexpr row; ty : 't; span : AMPCL.span }
  | MMatch of {
      value : 't mexpr;
      cases : ('t tpattern, 't mexpr) Ast.case list;
      ty : 't;
      span : AMPCL.span;
    }
  | MConstructor of {
      name : string;
      value : 't mexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | MNominalConstructor of {
      name : string;
      value : 't mexpr;
      ty : 't;
      span : AMPCL.span;
      id : int;
    }

type 't top_level =
  | MBind of {
      instantiations : SchemeEnv.t;
      name : 't tpattern;
      name_ty : 't;
      value : 't mexpr;
      span : AMPCL.span;
    }
  | MRecBind of {
      instantiations : SchemeEnv.t;
      name : 't tpattern;
      name_ty : 't;
      value : 't mexpr;
      span : AMPCL.span;
    }
  | MPrintString of string
  | MExpr of 't mexpr

let rec monomorphize_expr env = function
  | TVar { ident; ty; span } ->
      let scheme = SchemeEnv.find_opt ident env in
      Option.iter (fun scheme -> scheme := TypeEnv.add ident ty !scheme) scheme;
      MVar { ident; ty; span }
  | TFloat { value; ty; span } -> MFloat { value; ty; span }
  | TString { value; ty; span } -> MString { value; ty; span }
  | TInteger { value; ty; span } -> MInteger { value; ty; span }
  | TBoolean { value; ty; span } -> MBoolean { value; ty; span }
  | TUnit { ty; span } -> MUnit { ty; span }
  | TLambda { parameter; parameter_ty; body; ty; span } ->
      let body = monomorphize_expr env body in
      MLambda { parameter; parameter_ty; body; ty; span }
  | TApplication { lambda; arguement; ty; span } ->
      let lambda = monomorphize_expr env lambda in
      let arguement = monomorphize_expr env arguement in
      MApplication { lambda; arguement; ty; span }
  | TLet { name; name_ty; e1; e2; ty; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let e1 = monomorphize_expr env e1 in
      let e2 = monomorphize_expr (SchemeEnv.union instantiations env) e2 in
      MLet { name; name_ty; e1; e2; ty; span; instantiations }
  | TLetRec { name; name_ty; e1; e2; ty; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let env = SchemeEnv.union instantiations env in
      let e1 = monomorphize_expr env e1 in
      let e2 = monomorphize_expr env e2 in
      MLetRec { name; name_ty; e1; e2; ty; span; instantiations }
  | TIf { condition; consequent; alternative; ty; span } ->
      let condition = monomorphize_expr env condition in
      let consequent = monomorphize_expr env consequent in
      let alternative = monomorphize_expr env alternative in
      MIf { condition; consequent; alternative; ty; span }
  | TRecordAccess { record; projector; ty; span } ->
      let record = monomorphize_expr env record in
      MRecordAccess { record; projector; ty; span }
  | TRecordExtend { record; new_fields; ty; span } ->
      let record = monomorphize_expr env record in
      let new_fields =
        List.map
          (fun { label; value } ->
            let value = monomorphize_expr env value in

            { value; label })
          new_fields
      in
      MRecordExtend { record; new_fields; ty; span }
  | TRecord { fields; ty; span } ->
      let fields =
        List.map
          (fun { label; value } ->
            let value = monomorphize_expr env value in

            { value; label })
          fields
      in
      MRecord { fields; ty; span }
  | TMatch { value; cases; ty; span } ->
      let value = monomorphize_expr env value in
      let cases =
        List.map
          (fun { Ast.pattern; result } ->
            let result = monomorphize_expr env result in

            { Ast.pattern; result })
          cases
      in
      MMatch { value; cases; ty; span }
  | TConstructor { name; value; ty; span } ->
      let value = monomorphize_expr env value in
      MConstructor { name; value; ty; span }
  | TNominalConstructor { name; value; ty; span; id } ->
      let value = monomorphize_expr env value in
      MNominalConstructor { name; value; ty; span; id }

let monomorphize_tl env = function
  | TBind { name; name_ty; value; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let value = monomorphize_expr env value in

      let env = SchemeEnv.union instantiations env in
      (env, MBind { name; name_ty; value; span; instantiations })
  | TRecBind { name; name_ty; value; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let env = SchemeEnv.union instantiations env in

      let value = monomorphize_expr env value in
      (env, MRecBind { name; name_ty; value; span; instantiations })
  | TExpr expr ->
      let expr = monomorphize_expr env expr in
      (env, MExpr expr)
  | TPrintString s -> (env, MPrintString s)

let monomorphize_tls env tls = List.fold_left_map monomorphize_tl env tls |> snd
