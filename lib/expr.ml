open Types

type 'a row = (string * 'a) list

type pattern =
  | PVar of string
  | PWildcard
  | PNumber of float
  | PBoolean of bool
  | PRecord of pattern row
  (*   TODO: does record extension makes sense for patterns   *)
  | PConstructor of string * pattern

let rec pattern_to_string = function
  | PVar s -> s
  | PBoolean b -> string_of_bool b
  | PNumber n -> string_of_float n
  | PWildcard -> "_"
  | PRecord row ->
      "{ "
      ^ (row
        |> List.map (fun (label, pat) -> label ^ " = " ^ pattern_to_string pat)
        |> String.concat "; ")
      ^ " }"
  | PConstructor (name, pattern) ->
      name ^ " (" ^ pattern_to_string pattern ^ ")"

type 't tpattern =
  | PTVar of string * 't
  | PTWildcard of 't
  | PTNumber of float * 't
  | PTBoolean of bool * 't
  | PTRecord of 't tpattern row * 't
  | PTConstructor of string * 't tpattern * 't

let rec tpattern_to_string = function
  | PTVar (s, ty) -> s ^ " : " ^ type_to_string ty
  | PTBoolean (b, _) -> string_of_bool b
  | PTNumber (n, _) -> string_of_float n
  | PTWildcard _ -> "_"
  | PTRecord (row, _ty) ->
      "{ "
      ^ (row
        |> List.map (fun (label, pat) -> label ^ " = " ^ tpattern_to_string pat)
        |> String.concat "; ")
      ^ " }"
  | PTConstructor (name, pattern, _ty) ->
      name ^ " (" ^ tpattern_to_string pattern ^ ")"

let type_of_pattern pattern =
  match pattern with
  | PTVar (_, ty)
  | PTBoolean (_, ty)
  | PTNumber (_, ty)
  | PTRecord (_, ty)
  | PTConstructor (_, _, ty)
  | PTWildcard ty ->
      ty

type expr =
  | Var of string
  | Lambda of pattern * expr
  | Application of expr * expr
  | Let of pattern * expr * expr
  | LetRec of pattern * expr * expr
  | Unit
  | Boolean of bool
  | Number of float
  | RecordAccess of expr * string
  | RecordExtend of expr * expr row
  | Record of expr row
  | Constructor of string * expr
  | Match of expr * (pattern * expr) list
  | If of expr * expr * expr

type 't texpr =
  | TVar of string * 't
  | TNumber of float * 't
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

let rec expr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | Unit -> "()"
  | Var s -> s
  | Boolean b -> string_of_bool b
  | Number n -> string_of_float n
  | If (cond, cons, alt) ->
      "if ( " ^ expr_to_string indent cond ^ " )\n" ^ indent_string ^ "then ( "
      ^ expr_to_string next_level cons
      ^ " )\n" ^ indent_string ^ "else ( "
      ^ expr_to_string next_level alt
      ^ " )"
  | Let (var, e1, e2) ->
      "let " ^ pattern_to_string var ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
      ^ " )"
  | LetRec (var, e1, e2) ->
      "let rec " ^ pattern_to_string var ^ " = ( " ^ expr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ expr_to_string next_level e2
  | Lambda (var, abs) ->
      "\\" ^ pattern_to_string var ^ ".( " ^ expr_to_string indent abs ^ " )"
  | Application (abs, arg) ->
      "( " ^ expr_to_string indent abs ^ " ) ( " ^ expr_to_string indent arg
      ^ " )"
  | Record row ->
      "{\n"
      ^ (row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ expr_to_string indent pat)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordExtend (expr, row) ->
      "{" ^ expr_to_string indent expr ^ " with "
      ^ (row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ expr_to_string indent pat)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordAccess (record, label) -> expr_to_string indent record ^ "." ^ label
  | Constructor (name, expr) -> name ^ " (" ^ expr_to_string indent expr ^ ")"
  | Match (expr, cases) ->
      "match ( " ^ expr_to_string indent expr ^ " ) with \n"
      ^ indent_string
        (* we have an indent before the first case as it does not get indented by concat *)
      ^ (cases
        |> List.map (fun (pat, case) ->
               pattern_to_string pat ^ " -> " ^ expr_to_string next_level case)
        |> String.concat ("\n" ^ indent_string ^ "|"))

let expr_to_string = expr_to_string 0

let type_of expr =
  match expr with
  | TUnit ty
  | TVar (_, ty)
  | TBoolean (_, ty)
  | TNumber (_, ty)
  | TIf (_, _, _, ty)
  | TLet (_, _, _, _, ty)
  | TLetRec (_, _, _, _, ty)
  | TLambda (_, _, _, ty)
  | TRecordAccess (_, _, ty)
  | TApplication (_, _, ty)
  | TRecordExtend (_, _, ty)
  | TRecord (_, ty)
  | TMatch (_, _, ty)
  | TConstructor (_, _, ty) ->
      ty

let rec texpr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | TUnit _ -> "()"
  | TVar (s, _) -> s
  | TBoolean (b, _) -> string_of_bool b
  | TNumber (n, _) -> string_of_float n
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

(* let tterm_to_string = *)
(*   let rec inner = function *)
(*     | TVar (v, t) -> v ^ ": " ^ type_to_string t *)
(*     | TNumber (n, _) -> string_of_float n *)
(*     | TBoolean (b, _) -> string_of_bool b *)
(*     | TLambda (v, v_ty, typed_term, _) -> *)
(*         "(fun (" ^ tpattern_to_string v ^ ": " ^ type_to_string v_ty ^ ") -> " *)
(*         ^ inner typed_term ^ ")" *)
(*     | TApplication (f, a, _) -> "[" ^ inner f ^ " " ^ inner a ^ "]" *)
(*     | TUnit _ -> "()" *)
(*     | TRecord (row, _) -> *)
(*         "{ " *)
(*         ^ (row *)
(*           |> List.map (fun (label, value) -> label ^ " = " ^ inner value) *)
(*           |> String.concat "; ") *)
(*         ^ " }" *)
(*     | TRecordAccess (record, label, _ty) -> inner record ^ "." ^ label *)
(*     | TRecordExtend (expr, row, _) -> *)
(*         "{" ^ inner expr ^ " with " *)
(*         ^ (row *)
(*           |> List.map (fun (label, value) -> label ^ " = " ^ inner value) *)
(*           |> String.concat "; ") *)
(*         ^ "}" *)
(*     | TLet (v, v_ty, e1, e2, _) -> *)
(*         "let " ^ tpattern_to_string v ^ ": " ^ type_to_string v_ty ^ " = " *)
(*         ^ inner e1 ^ " in " ^ inner e2 *)
(*     | TConstructor (name, expr, _) -> name ^ " (" ^ inner expr ^ ")" *)
(*     | TMatch (expr, cases, _) -> *)
(*         "match ( " ^ inner expr *)
(*         ^ " ) with \n" *)
(*           (* we have an indent before the first case as it does not get indented by concat *) *)
(*         ^ (cases *)
(*           |> List.map (fun (pat, case) -> *)
(*                  tpattern_to_string pat ^ " -> " ^ inner case) *)
(*           |> String.concat "\n|") *)
(*   in *)
(*   inner *)
let texpr_to_string = texpr_to_string 0

type ('e, 'p) programF = Bind of 'p * 'e | Expr of 'e | RecBind of 'p * 'e

let program_to_string = function
  | Bind (name, expr) -> pattern_to_string name ^ " = " ^ expr_to_string expr
  | RecBind (name, expr) ->
      "rec" ^ pattern_to_string name ^ " = " ^ expr_to_string expr
  | Expr expr -> expr_to_string expr

let tprogram_to_string = function
  | Bind (name, expr) -> tpattern_to_string name ^ " = " ^ texpr_to_string expr
  | RecBind (name, expr) ->
      "rec" ^ tpattern_to_string name ^ " = " ^ texpr_to_string expr
  | Expr expr -> texpr_to_string expr

type program = (expr, pattern) programF
type 't tprogram = ('t texpr, 't tpattern) programF
