open Types
open Ast

type typed_ident = { ty : ty; ident : ident }

type typed_ast =
  | Unit of { ty : ty }
  | Float of { ty : ty; value : float }
  | Int of { ty : ty; value : int }
  | String of { ty : ty; value : string }
  | Ident of { ty : ty; ident : ident }
  | Application of { ty : ty; func : typed_ast; arguement : typed_ast }
  | Function of { ty : ty; parameter : typed_ident; abstraction : typed_ast }
  | If of {
      ty : ty;
      condition : typed_ast;
      consequent : typed_ast;
      alternative : typed_ast;
    }
  | Let of { ty : ty; name : ident; e1 : typed_ast; e2 : typed_ast }
  | Rec of { ty : ty; name : ident; expr : typed_ast }
  | Poly of { metas : int list; e : typed_ast }

type top_level =
  | Bind of { ty : ty; name : ident; value : typed_ast }
  | PrintString of string

type program = top_level list

(* we can make this non recursive if we make poly ast node store their type *)
let rec type_of expr =
  match expr with
  | Int a -> a.ty
  | Float a -> a.ty
  | String a -> a.ty
  | Ident a -> a.ty
  | Unit a -> a.ty
  | If a -> a.ty
  | Function a -> a.ty
  | Application a -> a.ty
  | Let a -> a.ty
  | Poly p -> TPoly (p.metas, type_of p.e)
  | Rec r -> r.ty

let rec ast_to_string ast =
  match ast with
  | Unit _ -> "()"
  | Float { value; _ } -> string_of_float value
  | Int { value; _ } -> string_of_int value
  | String { value; _ } -> value
  | Ident { ident; _ } -> ident
  | Application { func; arguement; _ } ->
      "( " ^ ast_to_string func ^ " " ^ ast_to_string arguement ^ " )"
  | If { condition; consequent; alternative; _ } ->
      "if " ^ ast_to_string condition ^ " then " ^ ast_to_string consequent
      ^ " else " ^ ast_to_string alternative
  | Let { name; e1; e2; _ } ->
      "let " ^ name ^ " = " ^ ast_to_string e1 ^ " in " ^ ast_to_string e2
  | Function { parameter; abstraction; _ } ->
      "fun (" ^ parameter.ident ^ ") -> " ^ ast_to_string abstraction
  | Poly p ->
      "∀"
      ^ String.concat "," (List.map string_of_int p.metas)
      ^ "." ^ ast_to_string p.e
  | Rec { name; expr; _ } -> "rec " ^ name ^ " " ^ ast_to_string expr

let print_program program =
  String.concat ""
    (List.map
       (fun exp ->
         match exp with
         | Bind { name; value; ty } ->
             "let " ^ name ^ " : " ^ type_to_string ty ^ " = "
             ^ ast_to_string value
         | PrintString s -> s)
       program)
