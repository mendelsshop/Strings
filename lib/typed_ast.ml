open Types
open Ast

type typed_ident = { ty : ty; ident : ident }
type 'b field = { name : string; value : 'b }
type ('a, 'b) projection = { ty : ty; value : 'a; projector : 'b }

type typed_pattern =
  | PFloat of { value : float; ty : ty }
  | PInt of { value : int; ty : ty }
  | PRecord of { fields : typed_pattern field list; ty : ty }
  | PString of { value : string; ty : ty }
  | PIdent of { ident : ident; ty : ty }
  | PConstructor of { name : string; value : typed_pattern; ty : ty }
  | PUnit of { ty : ty }
  | PWildCard of { ty : ty }

type typed_ast =
  | Unit of { ty : ty }
  | Float of { ty : ty; value : float }
  | Int of { ty : ty; value : int }
  | String of { ty : ty; value : string }
  | Ident of { ty : ty; ident : ident }
  | Application of { ty : ty; func : typed_ast; arguement : typed_ast }
  | Function of { ty : ty; parameter : typed_pattern; abstraction : typed_ast }
  | If of {
      ty : ty;
      condition : typed_ast;
      consequent : typed_ast;
      alternative : typed_ast;
    }
  | Let of { ty : ty; binding : typed_pattern; e1 : typed_ast; e2 : typed_ast }
  | Rec of { ty : ty; name : ident; expr : typed_ast }
  | Poly of { metas : int list; e : typed_ast }
  | Record of { ty : ty; fields : typed_ast field list }
  | RecordAcces of (typed_ast, string) projection
  | Constructor of { ty : ty; name : string; value : typed_ast }
  | Match of {
      expr : typed_ast;
      cases : (typed_pattern, typed_ast) case list;
      ty : ty;
    }

type top_level =
  | Bind of { binding : typed_pattern; value : typed_ast }
  | TypeBind of { name : string; ty : ty }
  | PrintString of string

type program = top_level list

let type_of_pattern pattern =
  match pattern with
  | PInt a -> a.ty
  | PFloat a -> a.ty
  | PString a -> a.ty
  | PIdent a -> a.ty
  | PUnit a -> a.ty
  | PRecord r -> r.ty
  | PWildCard t -> t.ty
  | PConstructor c -> c.ty

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
  | Record r -> r.ty
  | RecordAcces a -> a.ty
  | Constructor c -> c.ty
  | Match m -> m.ty

let rec pattern_to_string pattern =
  match pattern with
  | PFloat f -> string_of_float f.value
  | PInt i -> string_of_int i.value
  | PRecord r ->
      "( "
      ^ (r.fields
        |> List.map (fun { name; value } ->
               name ^ " = " ^ pattern_to_string value)
        |> String.concat ", ")
      ^ " )"
  | PString s -> "\"" ^ s.value ^ "\""
  | PIdent i -> i.ident ^ ": " ^ type_to_string i.ty
  | PConstructor { name; value; _ } ->
      name ^ "( " ^ pattern_to_string value ^ " )"
  | PUnit _ -> "()"
  | PWildCard { ty } -> "(_: " ^ type_to_string ty ^ ")"

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
  | Let { binding; e1; e2; _ } ->
      "let " ^ pattern_to_string binding ^ " = " ^ ast_to_string e1 ^ " in "
      ^ ast_to_string e2
  | Function { parameter; abstraction; _ } ->
      "fun ("
      ^ pattern_to_string parameter
      ^ ") -> " ^ ast_to_string abstraction
  | Poly p ->
      "∀"
      ^ String.concat "," (List.map string_of_int p.metas)
      ^ "." ^ ast_to_string p.e
  | Rec { name; expr; _ } -> "rec " ^ name ^ " " ^ ast_to_string expr
  | Record { fields; _ } ->
      "{ "
      ^ (fields
        |> List.map (function { name; value } ->
               name ^ ": " ^ ast_to_string value)
        |> String.concat " , ")
      ^ " }"
  | RecordAcces { value; projector; _ } -> ast_to_string value ^ "." ^ projector
  | Constructor { name; value; _ } -> name ^ " " ^ ast_to_string value
  | Match { expr; cases; _ } ->
      "match " ^ ast_to_string expr ^ " with "
      ^ String.concat " | "
          (cases
          |> List.map (fun { pattern; result } ->
                 pattern_to_string pattern ^ " -> " ^ ast_to_string result))

let top_level_to_string exp =
  match exp with
  | TypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
  | Bind { binding; value } ->
      "let (" ^ pattern_to_string binding ^ ") = " ^ ast_to_string value
  | PrintString s -> s

let print_program program =
  String.concat "" (List.map top_level_to_string program)
