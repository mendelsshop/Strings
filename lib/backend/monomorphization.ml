open Closure_conversion
open Typed_ast
open Types
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
  | MLocalVar of { ident : string; ty : 't; span : AMPCL.span }
  | MFloat of { value : float; ty : 't; span : AMPCL.span }
  | MString of { value : string; ty : 't; span : AMPCL.span }
  | MInteger of { value : int; ty : 't; span : AMPCL.span }
  | MBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | MLambda of { name : int; ty : 't; span : AMPCL.span }
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

type 't func = {
  parameter : 't tpattern;
  parameter_ty : 't;
  free_variables : 't StringMap.t;
  body : 't mexpr;
  ty : 't;
  span : AMPCL.span;
}

module FunctionEnv = Map.Make (Int)

type 't functions = ty func StringMap.t

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
  | LVar { ident; ty; span } ->
      let scheme = SchemeEnv.find_opt ident env in
      Option.iter (fun scheme -> scheme := TypeEnv.add ident ty !scheme) scheme;
      MVar { ident; ty; span }
  | LLocalVar { ident; ty; span } ->
      let scheme = SchemeEnv.find_opt ident env in
      Option.iter (fun scheme -> scheme := TypeEnv.add ident ty !scheme) scheme;
      MLocalVar { ident; ty; span }
  | LFloat { value; ty; span } -> MFloat { value; ty; span }
  | LString { value; ty; span } -> MString { value; ty; span }
  | LInteger { value; ty; span } -> MInteger { value; ty; span }
  | LBoolean { value; ty; span } -> MBoolean { value; ty; span }
  | LUnit { ty; span } -> MUnit { ty; span }
  | LLambda { name; ty; span } -> MLambda { name; ty; span }
  | LApplication { lambda; arguement; ty; span } ->
      let lambda = monomorphize_expr env lambda in
      let arguement = monomorphize_expr env arguement in
      MApplication { lambda; arguement; ty; span }
  | LLet { name; name_ty; e1; e2; ty; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let e1 = monomorphize_expr env e1 in
      let e2 = monomorphize_expr (SchemeEnv.union instantiations env) e2 in
      MLet { name; name_ty; e1; e2; ty; span; instantiations }
  | LLetRec { name; name_ty; e1; e2; ty; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let env = SchemeEnv.union instantiations env in
      let e1 = monomorphize_expr env e1 in
      let e2 = monomorphize_expr env e2 in
      MLetRec { name; name_ty; e1; e2; ty; span; instantiations }
  | LIf { condition; consequent; alternative; ty; span } ->
      let condition = monomorphize_expr env condition in
      let consequent = monomorphize_expr env consequent in
      let alternative = monomorphize_expr env alternative in
      MIf { condition; consequent; alternative; ty; span }
  | LRecordAccess { record; projector; ty; span } ->
      let record = monomorphize_expr env record in
      MRecordAccess { record; projector; ty; span }
  | LRecordExtend { record; new_fields; ty; span } ->
      let record = monomorphize_expr env record in
      let new_fields =
        List.map
          (fun { label; value } ->
            let value = monomorphize_expr env value in

            { value; label })
          new_fields
      in
      MRecordExtend { record; new_fields; ty; span }
  | LRecord { fields; ty; span } ->
      let fields =
        List.map
          (fun { label; value } ->
            let value = monomorphize_expr env value in

            { value; label })
          fields
      in
      MRecord { fields; ty; span }
  | LMatch { value; cases; ty; span } ->
      let value = monomorphize_expr env value in
      let cases =
        List.map
          (fun { Ast.pattern; result } ->
            let result = monomorphize_expr env result in

            { Ast.pattern; result })
          cases
      in
      MMatch { value; cases; ty; span }
  | LConstructor { name; value; ty; span } ->
      let value = monomorphize_expr env value in
      MConstructor { name; value; ty; span }
  | LNominalConstructor { name; value; ty; span; id } ->
      let value = monomorphize_expr env value in
      MNominalConstructor { name; value; ty; span; id }

let monomorphize_tl env = function
  | LBind { name; name_ty; value; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let value = monomorphize_expr env value in

      let env = SchemeEnv.union instantiations env in
      (env, MBind { name; name_ty; value; span; instantiations })
  | LRecBind { name; name_ty; value; span } ->
      let instantiations =
        get_binders name
        |> List.map (fun name -> (name, ref TypeEnv.empty))
        |> SchemeEnv.of_list
      in
      let env = SchemeEnv.union instantiations env in

      let value = monomorphize_expr env value in
      (env, MRecBind { name; name_ty; value; span; instantiations })
  | LExpr expr ->
      let expr = monomorphize_expr env expr in
      (env, MExpr expr)
  | LPrintString s -> (env, MPrintString s)

let monomorphize_tls env tls = List.fold_left_map monomorphize_tl env tls |> snd
