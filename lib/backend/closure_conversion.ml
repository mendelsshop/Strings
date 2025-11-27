open Typed_ast
open Monomorphization
open Types
module TypeEnv = Infer.SimpleTypeEnv
open Utils

type 't lexpr =
  | LVar of { ident : string; ty : 't; span : AMPCL.span }
  | LLocalVar of { ident : string; ty : 't; span : AMPCL.span }
  | LFloat of { value : float; ty : 't; span : AMPCL.span }
  | LString of { value : string; ty : 't; span : AMPCL.span }
  | LInteger of { value : int; ty : 't; span : AMPCL.span }
  | LBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | LLambda of { name : int; ty : 't; span : AMPCL.span }
  | LMulti of { types : 't lexpr list; original : 't mexpr; ty : 't }
  | LSelect of { value : 't lexpr; selector : int; ty : 't }
  | LApplication of {
      lambda : 't lexpr;
      arguement : 't lexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | LUnit of { ty : 't; span : AMPCL.span }
  | LLet of {
      name : 't tpattern;
      name_ty : 't;
      e1 : 't lexpr;
      e2 : 't lexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | LLetRec of {
      name : 't tpattern;
      name_ty : 't;
      e1 : 't lexpr;
      e2 : 't lexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | LIf of {
      condition : 't lexpr;
      consequent : 't lexpr;
      alternative : 't lexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | LRecordAccess of {
      record : 't lexpr;
      projector : string;
      ty : 't;
      span : AMPCL.span;
    }
  | LRecordExtend of {
      record : 't lexpr;
      new_fields : 't lexpr row;
      ty : 't;
      span : AMPCL.span;
    }
  | LRecord of { fields : 't lexpr row; ty : 't; span : AMPCL.span }
  | LMatch of {
      value : 't lexpr;
      cases : ('t tpattern, 't lexpr) Ast.case list;
      ty : 't;
      span : AMPCL.span;
    }
  | LConstructor of {
      name : string;
      value : 't lexpr;
      ty : 't;
      span : AMPCL.span;
    }
  | LNominalConstructor of {
      name : string;
      value : 't lexpr;
      ty : 't;
      span : AMPCL.span;
      id : int;
    }

type 't func = {
  parameter : 't tpattern;
  parameter_ty : 't;
  free_variables : 't StringMap.t;
  body : 't lexpr;
  ty : 't;
  span : AMPCL.span;
}

module FunctionEnv = Env.Make (Int)

type 't functions = ty func StringMap.t

type 't top_level =
  | LBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't lexpr;
      span : AMPCL.span;
    }
  | LRecBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't lexpr;
      span : AMPCL.span;
    }
  | LPrintString of string
  | LExpr of 't lexpr

let type_of_expr = function
  | LLocalVar { ty; _ }
  | LVar { ty; _ }
  | LFloat { ty; _ }
  | LString { ty; _ }
  | LInteger { ty; _ }
  | LBoolean { ty; _ }
  | LLambda { ty; _ }
  | LApplication { ty; _ }
  | LUnit { ty; _ }
  | LLet { ty; _ }
  | LLetRec { ty; _ }
  | LIf { ty; _ }
  | LRecordAccess { ty; _ }
  | LRecordExtend { ty; _ }
  | LRecord { ty; _ }
  | LMatch { ty; _ }
  | LConstructor { ty; _ }
  | LSelect { ty; _ }
  | LMulti { ty; _ }
  | LNominalConstructor { ty; _ } ->
      ty

let rec closure_convert_expr immediate_env functions = function
  | MVar { ident; ty; span } ->
      ( (if List.mem ident immediate_env then LLocalVar { ident; ty; span }
         else LVar { ident; ty; span }),
        TypeEnv.singleton ident ty,
        functions )
  | MFloat { value; ty; span } ->
      (LFloat { value; ty; span }, TypeEnv.empty, functions)
  | MString { value; ty; span } ->
      (LString { value; ty; span }, TypeEnv.empty, functions)
  | MInteger { value; ty; span } ->
      (LInteger { value; ty; span }, TypeEnv.empty, functions)
  | MBoolean { value; ty; span } ->
      (LBoolean { value; ty; span }, TypeEnv.empty, functions)
  | MUnit { ty; span } -> (LUnit { ty; span }, TypeEnv.empty, functions)
  | MSelect { selector; value; ty } ->
      let value, ftv, functions =
        closure_convert_expr immediate_env functions value
      in
      (LSelect { selector; value; ty }, ftv, functions)
  | MMulti { original; types; ty } ->
      let (ftv, functions), types =
        List.fold_left_map
          (fun (ftv, functions) instance ->
            let instance, ftv', functions =
              closure_convert_expr immediate_env functions instance
            in

            ((TypeEnv.union ftv ftv', functions), instance))
          (TypeEnv.empty, functions) types
      in
      (LMulti { original; types; ty }, ftv, functions)
  | MLambda { parameter; parameter_ty; body; ty; span } ->
      let body, ftv, functions =
        closure_convert_expr (get_binders parameter) functions body
      in
      let ftv =
        List.fold_left (Fun.flip TypeEnv.remove) ftv (get_binders parameter)
      in

      let name = gensym_int () in
      let lambda =
        { parameter; parameter_ty; body; ty; span; free_variables = ftv }
      in
      (LLambda { name; ty; span }, ftv, FunctionEnv.add name lambda functions)
  | MApplication { lambda; arguement; ty; span } ->
      let lambda, ftv, functions =
        closure_convert_expr immediate_env functions lambda
      in
      let arguement, ftv', functions =
        closure_convert_expr immediate_env functions arguement
      in

      ( LApplication { lambda; arguement; ty; span },
        TypeEnv.union ftv ftv',
        functions )
  | MLet { name; name_ty; e1; e2; ty; span; _ } ->
      let e1, ftv, functions =
        closure_convert_expr immediate_env functions e1
      in
      let e2, ftv', functions =
        closure_convert_expr (get_binders name @ immediate_env) functions e2
      in
      let ftv' =
        List.fold_left (Fun.flip TypeEnv.remove) ftv' (get_binders name)
      in
      ( LLet { name; name_ty; e1; e2; ty; span },
        TypeEnv.union ftv ftv',
        functions )
  | MLetRec { name; name_ty; e1; e2; ty; span; _ } ->
      let e1, ftv, functions =
        closure_convert_expr (get_binders name @ immediate_env) functions e1
      in
      let e2, ftv', functions =
        closure_convert_expr (get_binders name @ immediate_env) functions e2
      in
      let ftv =
        List.fold_left (Fun.flip TypeEnv.remove) (TypeEnv.union ftv ftv')
          (get_binders name)
      in
      ( LLetRec { name; name_ty; e1; e2; ty; span },
        TypeEnv.union ftv ftv',
        functions )
  | MIf { condition; consequent; alternative; ty; span } ->
      let condition, ftv, functions =
        closure_convert_expr immediate_env functions condition
      in
      let consequent, ftv', functions =
        closure_convert_expr immediate_env functions consequent
      in
      let alternative, ftv'', functions =
        closure_convert_expr immediate_env functions alternative
      in
      ( LIf { condition; consequent; alternative; ty; span },
        TypeEnv.union (TypeEnv.union ftv ftv') ftv'',
        functions )
  | MRecordAccess { record; projector; ty; span } ->
      let record, ftv, functions =
        closure_convert_expr immediate_env functions record
      in
      (LRecordAccess { record; projector; ty; span }, ftv, functions)
  | MRecordExtend { record; new_fields; ty; span } ->
      let record, ftv, functions =
        closure_convert_expr immediate_env functions record
      in
      let (ftv, functions), new_fields =
        List.fold_left_map
          (fun (ftv, functions) { label; value } ->
            let value, ftv', functions =
              closure_convert_expr immediate_env functions value
            in

            ((TypeEnv.union ftv ftv', functions), { value; label }))
          (ftv, functions) new_fields
      in
      (LRecordExtend { record; new_fields; ty; span }, ftv, functions)
  | MRecord { fields; ty; span } ->
      let (ftv, functions), fields =
        List.fold_left_map
          (fun (ftv, functions) { label; value } ->
            let value, ftv', functions =
              closure_convert_expr immediate_env functions value
            in

            ((TypeEnv.union ftv ftv', functions), { value; label }))
          (TypeEnv.empty, functions) fields
      in
      (LRecord { fields; ty; span }, ftv, functions)
  | MMatch { value; cases; ty; span } ->
      let value, ftv, functions =
        closure_convert_expr immediate_env functions value
      in
      let (ftv, functions), cases =
        List.fold_left_map
          (fun (ftv, functions) { Ast.pattern; result } ->
            let result, ftv', functions =
              closure_convert_expr immediate_env functions result
            in

            ((TypeEnv.union ftv ftv', functions), { Ast.pattern; result }))
          (ftv, functions) cases
      in
      (LMatch { value; cases; ty; span }, ftv, functions)
  | MConstructor { name; value; ty; span } ->
      let value, ftv, functions =
        closure_convert_expr immediate_env functions value
      in
      (LConstructor { name; value; ty; span }, ftv, functions)
  | MNominalConstructor { name; value; ty; span; id } ->
      let value, ftv, functions =
        closure_convert_expr immediate_env functions value
      in
      (LNominalConstructor { name; value; ty; span; id }, ftv, functions)

let closure_convert_tl immediate_env functions = function
  | MBind { name; name_ty; value; span; _ } ->
      let value, _, functions =
        closure_convert_expr immediate_env functions value
      in

      ( (immediate_env @ get_binders name, functions),
        LBind { name; name_ty; value; span } )
  | MRecBind { name; name_ty; value; span; _ } ->
      let value, _, functions =
        closure_convert_expr (get_binders name @ immediate_env) functions value
      in
      ( (immediate_env @ get_binders name, functions),
        LRecBind { name; name_ty; value; span } )
  | MExpr expr ->
      let expr, _, functions =
        closure_convert_expr immediate_env functions expr
      in
      ((immediate_env, functions), LExpr expr)
  | MPrintString s -> ((immediate_env, functions), LPrintString s)

let closure_convert_tls ?(immediate_env = []) tls =
  let (_, functions), tls =
    List.fold_left_map
      (fun (immediate_env, functions) tl ->
        closure_convert_tl immediate_env functions tl)
      (immediate_env, FunctionEnv.empty)
      tls
  in
  (functions, tls)
