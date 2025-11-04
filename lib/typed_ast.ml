open Types
open Utils

type 't tpattern =
  | PTVar of { ident : string; ty : 't; span : AMPCL.span }
  | PTString of { value : string; ty : 't; span : AMPCL.span }
  | PTWildcard of { ty : 't; span : AMPCL.span }
  | PTInteger of { value : int; ty : 't; span : AMPCL.span }
  | PTFloat of { value : float; ty : 't; span : AMPCL.span }
  | PTBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | PTRecord of { fields : 't tpattern row; ty : 't; span : AMPCL.span }
  | PTConstructor of {
      name : string;
      value : 't tpattern;
      ty : 't;
      span : AMPCL.span;
    }
  | PTNominalConstructor of {
      name : string;
      value : 't tpattern;
      ty : 't;
      id : int;
      span : AMPCL.span;
    }
  | PTUnit of { ty : 't; span : AMPCL.span }
  | PTOr of { patterns : 't tpattern list; ty : 't; span : AMPCL.span }
  | PTAs of { name : string; value : 't tpattern; ty : 't; span : AMPCL.span }

module ConstExpr (T : sig
  type t
end) =
struct
  type t = { value : T.t; ty : ty; span : AMPCL.span }
end

module StringExpr = ConstExpr (String)
module IntegerExpr = ConstExpr (Int)
module FloatExpr = ConstExpr (Float)
module BooleanExpr = ConstExpr (Bool)

module UnitExpr = struct
  type t = { ty : ty; span : AMPCL.span }
end

module VarExpr = struct
  type t = { ident : string; ty : ty; span : AMPCL.span }
end

module LetExpr = struct
  type 't t = {
    name : ty tpattern;
    name_ty : ty;
    e1 : 't;
    e2 : 't;
    ty : ty;
    span : AMPCL.span;
  }
end

module ApplicationExpr = struct
  type 't t = { lambda : 't; arguement : 't; ty : ty; span : AMPCL.span }
end

module LetRecExpr = struct
  type 't t = {
    name : ty tpattern;
    name_ty : ty;
    e1 : 't;
    e2 : 't;
    ty : ty;
    span : AMPCL.span;
  }
end

module LambdaExpr = struct
  type 't t = {
    parameter : ty tpattern;
    parameter_ty : ty;
    body : 't;
    ty : ty;
    span : AMPCL.span;
  }
end

module IfExpr = struct
  type 't t = {
    condition : 't;
    consequent : 't;
    alternative : 't;
    ty : ty;
    span : AMPCL.span;
  }
end

module RecordAccessExpr = struct
  type 't t = { record : 't; projector : string; ty : ty; span : AMPCL.span }
end

module RecordExtendExpr = struct
  type 't t = { record : 't; new_fields : 't row; ty : ty; span : AMPCL.span }
end

module RecordExpr = struct
  type 't t = { fields : 't row; ty : ty; span : AMPCL.span }
end

module MatchExpr = struct
  type 't t = {
    value : 't;
    cases : (ty tpattern, 't) Ast.case list;
    ty : ty;
    span : AMPCL.span;
  }
end

module ConstructorExpr = struct
  type 't t = { name : string; value : 't; ty : ty; span : AMPCL.span }
end

module NominalConstructorExpr = struct
  type 't t = {
    name : string;
    value : 't;
    ty : ty;
    span : AMPCL.span;
    id : int;
  }
end

type texpr =
  [ `TVar of VarExpr.t
  | `TFloat of FloatExpr.t
  | `TString of StringExpr.t
  | `TInteger of IntegerExpr.t
  | `TBoolean of BooleanExpr.t
  | `TLambda of texpr LambdaExpr.t
  | `TLet of texpr LetExpr.t
  | `TApplication of texpr ApplicationExpr.t
  | `TUnit of UnitExpr.t
  | `TLetRec of texpr LetRecExpr.t
  | `TIf of texpr IfExpr.t
  | `TRecordAccess of texpr RecordAccessExpr.t
  | `TRecordExtend of texpr RecordExtendExpr.t
  | `TRecord of texpr RecordExpr.t
  | `TMatch of texpr MatchExpr.t
  | `TConstructor of texpr ConstructorExpr.t
  | `TNominalConstructor of texpr NominalConstructorExpr.t ]

type texpr' =
  [ `TVar of UnitExpr.t
  | `TFloat of FloatExpr.t
  | `TString of StringExpr.t
  | `TInteger of IntegerExpr.t
  | `TBoolean of BooleanExpr.t
  | `TLambda of 't LambdaExpr.t
  | `TLet of 't LetExpr.t
  | `TApplication of 't ApplicationExpr.t
  | `TUnit of UnitExpr.t
  | `TLetRec of 't LetRecExpr.t
  | `TIf of 't IfExpr.t
  | `TRecordAccess of 't RecordAccessExpr.t
  | `TRecordExtend of 't RecordExtendExpr.t
  | `TRecord of 't RecordExpr.t
  | `TMatch of 't MatchExpr.t
  | `TConstructor of 't ConstructorExpr.t
  | `TNominalConstructor of 't NominalConstructorExpr.t ]
  as
  't

let convert : texpr -> texpr' = function
  | (`TString _ | `TFloat _ | `TBoolean _ | `TInteger _ | `TUnit _) as f -> f
  | `TLet _ | `TLambda _ | `TRecordAccess _ | `TLetRec _ | `TApplication _
  | `TRecordExtend _ | `TVar _ | `TMatch _ | `TRecord _ | `TNominalConstructor _
  | `TConstructor _ | `TIf _ ->
      failwith ""

type 't top_level =
  | TBind of {
      name : 't tpattern;
      name_ty : 't;
      value : texpr;
      span : AMPCL.span;
    }
  | TRecBind of {
      name : 't tpattern;
      name_ty : 't;
      value : texpr;
      span : AMPCL.span;
    }
  | TPrintString of string
  | TExpr of texpr

let type_of_expr : texpr -> _ = function
  | `TVar { ty; _ }
  | `TFloat { ty; _ }
  | `TString { ty; _ }
  | `TInteger { ty; _ }
  | `TBoolean { ty; _ }
  | `TLambda { ty; _ }
  | `TApplication { ty; _ }
  | `TUnit { ty; _ }
  | `TLet { ty; _ }
  | `TLetRec { ty; _ }
  | `TIf { ty; _ }
  | `TRecordAccess { ty; _ }
  | `TRecordExtend { ty; _ }
  | `TRecord { ty; _ }
  | `TMatch { ty; _ }
  | `TConstructor { ty; _ }
  | `TNominalConstructor { ty; _ } ->
      ty

type 't program = 't top_level list

let span_of_pattern : 't tpattern -> AMPCL.span = function
  | PTVar { span; _ }
  | PTNominalConstructor { span; _ }
  | PTUnit { span; _ }
  | PTWildcard { span; _ }
  | PTFloat { span; _ }
  | PTInteger { span; _ }
  | PTBoolean { span; _ }
  | PTRecord { span; _ }
  | PTConstructor { span; _ }
  | PTString { span; _ }
  | PTOr { span; _ }
  | PTAs { span; _ } ->
      span
(* we can make this non recursive if we make poly ast node store their type *)

let rec tpattern_to_string = function
  | PTVar { ident; ty; _ } -> ident ^ " : " ^ type_to_string ty
  | PTString { value; _ } -> value
  | PTUnit _ -> "()"
  | PTBoolean { value; _ } -> string_of_bool value
  | PTFloat { value; _ } -> string_of_float value
  | PTInteger { value; _ } -> string_of_int value
  | PTWildcard _ -> "_"
  | PTRecord { fields; _ } ->
      "{ "
      ^ (fields
        |> List.map (fun { label; value } ->
            label ^ " = " ^ tpattern_to_string value)
        |> String.concat "; ")
      ^ " }"
  | PTConstructor { name; value; _ } ->
      "`" ^ name ^ " (" ^ tpattern_to_string value ^ ")"
  | PTNominalConstructor { name; value; _ } ->
      name ^ " (" ^ tpattern_to_string value ^ ")"
  | PTAs { name; value; _ } -> name ^ " as " ^ tpattern_to_string value
  | PTOr { patterns; _ } ->
      List.map tpattern_to_string patterns |> String.concat " | "

let rec texpr_to_string indent : texpr -> _ =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | `TUnit _ -> "()"
  | `TVar { ident; _ } -> ident
  | `TString { value; _ } -> value
  | `TInteger { value; _ } -> string_of_int value
  | `TFloat { value; _ } -> string_of_float value
  | `TBoolean { value; _ } -> string_of_bool value
  | `TIf { condition; consequent; alternative; _ } ->
      "if ( "
      ^ texpr_to_string indent condition
      ^ " )\n" ^ indent_string ^ "then ( "
      ^ texpr_to_string next_level consequent
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ texpr_to_string next_level alternative
      ^ " )"
  | `TLet { name; e1; e2; _ } ->
      "let " ^ tpattern_to_string name ^ " = ( " ^ texpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ texpr_to_string next_level e2
      ^ " )"
  | `TLetRec { name; e1; e2; _ } ->
      "let rec " ^ tpattern_to_string name ^ " = ( " ^ texpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ texpr_to_string next_level e2
      ^ " )"
  | `TLambda { parameter; body; _ } ->
      "\\"
      ^ tpattern_to_string parameter
      ^ ".( "
      ^ texpr_to_string indent body
      ^ " )"
  | `TApplication { lambda; arguement; _ } ->
      "( "
      ^ texpr_to_string indent lambda
      ^ " ) ( "
      ^ texpr_to_string indent arguement
      ^ " )"
  | `TRecord { fields; _ } ->
      "{\n"
      ^ (fields
        |> List.map (fun { label; value } ->
            indent_string ^ label ^ " = " ^ texpr_to_string next_level value)
        |> String.concat ";\n")
      ^ "\n}"
  | `TRecordAccess { record; projector; _ } ->
      texpr_to_string indent record ^ "." ^ projector
  | `TConstructor { name; value; _ } ->
      "`" ^ name ^ " (" ^ texpr_to_string indent value ^ ")"
  | `TNominalConstructor { name; value; _ } ->
      name ^ " (" ^ texpr_to_string indent value ^ ")"
  | `TMatch { value; cases; _ } ->
      "match ( "
      ^ texpr_to_string indent value
      ^ " ) with \n"
      ^ indent_string
        (* we have an indent before the first case as it does not get indented by concat *)
      ^ (cases
        |> List.map (fun { Ast.pattern; result } ->
            tpattern_to_string pattern ^ " -> "
            ^ texpr_to_string next_level result)
        |> String.concat ("\n" ^ indent_string ^ "|"))
  | `TRecordExtend { record; new_fields; _ } ->
      "{"
      ^ texpr_to_string indent record
      ^ " with "
      ^ (new_fields
        |> List.map (fun { label; value } ->
            indent_string ^ label ^ " = " ^ texpr_to_string indent value)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"

let texpr_to_string = texpr_to_string 0

let top_level_to_string exp =
  match exp with
  | TExpr expr -> texpr_to_string expr
  | TRecBind { name; value; _ } ->
      "let rec " ^ tpattern_to_string name ^ " = " ^ texpr_to_string value
  | TBind { name; value; _ } ->
      "let (" ^ tpattern_to_string name ^ ") = " ^ texpr_to_string value
  | TPrintString s -> s

let program_to_string program =
  String.concat "\n" (List.map top_level_to_string program)
