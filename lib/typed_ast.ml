open Types

type 'b field = { name : string; value : 'b }
type ('a, 'b) projection = { ty : ty; value : 'a; projector : 'b }
type 'a row = (string * 'a) list

type 't tpattern =
  | PTVar of string * 't
  | PTString of (string * 't)
  | PTWildcard of 't
  | PTInteger of int * 't
  | PTFloat of float * 't
  | PTBoolean of bool * 't
  | PTRecord of 't tpattern row * 't
  | PTConstructor of string * 't tpattern * 't
  | PTUnit of ty

type 't texpr =
  | TVar of string * 't
  | TFloat of (float * 't)
  | TString of (string * 't)
  | TInteger of (int * 't)
  | TBoolean of bool * 't
  | TLambda of 't tpattern * 't * 't texpr * 't
  | TApplication of 't texpr * 't texpr * 't
  | TUnit of 't
  | TLet of 't tpattern * 't * 't texpr * 't texpr * 't
  | TLetRec of 't tpattern * 't * 't texpr * 't texpr * 't
  | TIf of 't texpr * 't texpr * 't texpr * ty
  | TRecordAccess of 't texpr * string * 't
  | TRecordExtend of 't texpr * 't texpr row * 't
  | TRecord of 't texpr row * 't
  | TMatch of 't texpr * ('t tpattern * 't texpr) list * 't
  | TConstructor of string * 't texpr * 't

type 't top_level =
  | TBind of { binding : 't tpattern; value : 't texpr }
  | TRecBind of { binding : 't tpattern; value : 't texpr }
  | TTypeBind of { name : string; ty : ty }
  | TPrintString of string

type 't program = 't top_level list

(* we can make this non recursive if we make poly ast node store their type *)

let rec tpattern_to_string = function
  | PTVar (s, ty) -> s ^ " : " ^ type_to_string ty
  | PTString (s, _) -> s
  | PTUnit _ -> "()"
  | PTBoolean (b, _) -> string_of_bool b
  | PTFloat (n, _) -> string_of_float n
  | PTInteger (n, _) -> string_of_int n
  | PTWildcard _ -> "_"
  | PTRecord (row, _ty) ->
      "{ "
      ^ (row
        |> List.map (fun (label, pat) -> label ^ " = " ^ tpattern_to_string pat)
        |> String.concat "; ")
      ^ " }"
  | PTConstructor (name, pattern, _ty) ->
      name ^ " (" ^ tpattern_to_string pattern ^ ")"

let rec texpr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | TUnit _ -> "()"
  | TVar (s, _) -> s
  | TString (s, _) -> s
  | TInteger (n, _) -> string_of_int n
  | TFloat (n, _) -> string_of_float n
  | TBoolean (b, _) -> string_of_bool b
  | TIf (cond, cons, alt, _) ->
      "if ( "
      ^ texpr_to_string indent cond
      ^ " )\n" ^ indent_string ^ "then ( "
      ^ texpr_to_string next_level cons
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ texpr_to_string next_level alt
      ^ " )"
  | TLet (var, _, e1, e2, _) ->
      "let " ^ tpattern_to_string var ^ " = ( " ^ texpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ texpr_to_string next_level e2
      ^ " )"
  | TLetRec (var, _, e1, e2, _) ->
      "let rec " ^ tpattern_to_string var ^ " = ( " ^ texpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ texpr_to_string next_level e2
      ^ " )"
  | TLambda (var, _, abs, _) ->
      "\\" ^ tpattern_to_string var ^ ".( " ^ texpr_to_string indent abs ^ " )"
  | TApplication (abs, arg, _) ->
      "( " ^ texpr_to_string indent abs ^ " ) ( " ^ texpr_to_string indent arg
      ^ " )"
  | TRecord (row, _ty) ->
      "{\n"
      ^ (row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ texpr_to_string next_level pat)
        |> String.concat ";\n")
      ^ "\n}"
  | TRecordAccess (record, label, _ty) ->
      texpr_to_string indent record ^ "." ^ label
  | TConstructor (name, expr, _ty) ->
      name ^ " (" ^ texpr_to_string indent expr ^ ")"
  | TMatch (expr, cases, _) ->
      "match ( "
      ^ texpr_to_string indent expr
      ^ " ) with \n"
      ^ indent_string
        (* we have an indent before the first case as it does not get indented by concat *)
      ^ (cases
        |> List.map (fun (pat, case) ->
               tpattern_to_string pat ^ " -> " ^ texpr_to_string next_level case)
        |> String.concat ("\n" ^ indent_string ^ "|"))
  | TRecordExtend (expr, row, _) ->
      "{"
      ^ texpr_to_string indent expr
      ^ " with "
      ^ (row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ texpr_to_string indent pat)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"

let texpr_to_string = texpr_to_string 0

let top_level_to_string exp =
  match exp with
  | TTypeBind { name; ty } -> "type " ^ name ^ " = " ^ type_to_string ty
  | TRecBind { binding; value } ->
      "let rec" ^ tpattern_to_string binding ^ " = " ^ texpr_to_string value
  | TBind { binding; value } ->
      "let (" ^ tpattern_to_string binding ^ ") = " ^ texpr_to_string value
  | TPrintString s -> s

let print_program program =
  String.concat "\n" (List.map top_level_to_string program)
