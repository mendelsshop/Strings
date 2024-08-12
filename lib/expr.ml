module MetaVariables = Set.Make (String)
module Row = Map.Make (String)

module Types = struct
  type ty =
    | TInt
    | TBool
    | TArrow of ty * ty
    | TMeta of string
    | TTuple of ty * ty
    (*TODO: seperate row types, also would help with printing*)
    | TRowEmpty
    | TRowExtend of string * ty * ty
    | TRecord of ty
    | TPoly of MetaVariables.t * ty

  let rec type_to_string ?(type_delim = ": ") ?(delim = "; ") ?(unit = "{}") =
    function
    | TInt -> "number"
    | TBool -> "boolean"
    | TArrow (t1, t2) -> type_to_string t1 ^ " -> " ^ type_to_string t2
    | TMeta m -> m
    | TTuple (t1, t2) ->
        "( " ^ type_to_string t1 ^ " * " ^ type_to_string t2 ^ " )"
    | TPoly (metas, ty) ->
        (if MetaVariables.is_empty metas then ""
         else "∀" ^ (MetaVariables.to_list metas |> String.concat ", ") ^ ".")
        ^ type_to_string ty
    | TRecord t -> "{ " ^ type_to_string ~unit:"" t ^ " }"
    | TRowExtend (label, field, row_extension) ->
        label ^ type_delim ^ type_to_string field ^ delim
        ^ type_to_string row_extension ~type_delim ~delim ~unit
    | TRowEmpty -> unit
end

open Types

type pattern =
  | PVar of string
  | PWildcard
  | PNumber of float
  | PBoolean of bool
  | PTuple of pattern * pattern
  | PRecord of pattern Row.t

let rec pattern_to_string = function
  | PVar s -> s
  | PBoolean b -> string_of_bool b
  | PNumber n -> string_of_float n
  | PWildcard -> "_"
  | PTuple (e1, e2) ->
      "( " ^ pattern_to_string e1 ^ " , " ^ pattern_to_string e2 ^ " )"
  | PRecord row ->
      "{ "
      ^ (Row.to_list row
        |> List.map (fun (label, pat) -> label ^ " = " ^ pattern_to_string pat)
        |> String.concat "; ")
      ^ " }"
(*| PRecord row -> *)

type tpattern =
  | PTVar of string * ty
  | PTWildcard of ty
  | PTNumber of float * ty
  | PTBoolean of bool * ty
  | PTTuple of tpattern * tpattern * ty
  | PTPoly of MetaVariables.t * tpattern
  | PTRecord of tpattern Row.t * ty

let rec tpattern_to_string = function
  | PTVar (s, ty) -> s ^ " : " ^ type_to_string ty
  | PTBoolean (b, _) -> string_of_bool b
  | PTNumber (n, _) -> string_of_float n
  | PTWildcard _ -> "_"
  | PTTuple (e1, e2, _) ->
      "( " ^ tpattern_to_string e1 ^ " , " ^ tpattern_to_string e2 ^ " )"
  | PTPoly (metas, pat) ->
      (if MetaVariables.is_empty metas then ""
       else "∀" ^ (MetaVariables.to_list metas |> String.concat ", ") ^ ".")
      ^ tpattern_to_string pat
  | PTRecord (row, _ty) ->
      "{ "
      ^ (Row.to_list row
        |> List.map (fun (label, pat) -> label ^ " = " ^ tpattern_to_string pat)
        |> String.concat "; ")
      ^ " }"

let rec type_of_pattern pattern =
  match pattern with
  | PTVar (_, ty)
  | PTBoolean (_, ty)
  | PTNumber (_, ty)
  | PTTuple (_, _, ty)
  | PTRecord (_, ty)
  | PTWildcard ty ->
      ty
  | PTPoly (metas, expr) -> TPoly (metas, type_of_pattern expr)

(*type 'a exprF =*)
(*  | Var of string*)
(*  | Boolean of bool*)
(*  | Number of float*)
(*  | TIf of 'a * 'a * 'a*)
(*  | Let of string * 'a * 'a*)
(*  | Lambda of string * 'a*)
(*  | Application of 'a * 'a*)
(**)
(*type expr = Exp of expr exprF*)
(*type texpr = TExp of (texpr * ty) exprF*)
(**)
(*let _ : expr = Exp (Let ("x", Exp (Number 5.0), Exp (Var "x")))*)
(**)
(*type 'a exprF' =*)
(*  | Var of 'a * string*)
(*  | Boolean of 'a * bool*)
(*  | Number of 'a * float*)
(*  | If of 'a exprF' * 'a exprF' * 'a exprF'*)
(*  | Let of 'a * string * 'a exprF' * 'a exprF'*)
(*  | Lambda of 'a * string * 'a exprF'*)
(*  | Application of 'a * 'a exprF' * 'a exprF'*)
(**)
(*type expr' = unit exprF'*)
(*type texpr' = ty exprF'*)
(**)
(*let _ : expr' = Let ((), "x", Number ((), 5.0), Var ((), "x"))*)
(**)
(*type 'a exprF'' = 'a exprF''' * 'a*)
(**)
(*and 'a exprF''' =*)
(*  | Num of float*)
(*  | Bool of bool*)
(*  | Var of string*)
(*  | If of 'a exprF'' * 'a exprF'' * 'a exprF''*)
(*  | Lambda of string * 'a exprF''*)
(*  | Let of string * 'a exprF'' * 'a exprF''*)
(*  | App of 'a exprF'' * 'a exprF''*)
(**)
(*type expr'' = unit exprF''*)
(*type texpr'' = ty exprF''*)
(**)
(*let _ : expr'' = (Let ("x", (Num 5.0, ()), (Var "x", ())), ())*)

type expr =
  | Var of string
  | Boolean of bool
  | Number of float
  | If of expr * expr * expr
  | Let of pattern * expr * expr
  | Lambda of pattern * expr
  | Application of expr * expr
  | Tuple of expr * expr
  | Record of expr Row.t
  | RecordAcces of expr * string

(*bad expression format*)
let rec expr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
  | Var s -> s
  | Boolean b -> string_of_bool b
  | Number n -> string_of_float n
  | Tuple (e1, e2) ->
      "( " ^ expr_to_string indent e1 ^ " , " ^ expr_to_string indent e2 ^ " )"
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
  | Lambda (var, abs) ->
      "\\" ^ pattern_to_string var ^ ".( " ^ expr_to_string indent abs ^ " )"
  | Application (abs, arg) ->
      "( " ^ expr_to_string indent abs ^ " ) ( " ^ expr_to_string indent arg
      ^ " )"
  | Record row ->
      "{\n"
      ^ (Row.to_list row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ expr_to_string indent pat)
        |> String.concat "; ")
      ^ "\n" ^ indent_string ^ "}"
  | RecordAcces (record, label) -> expr_to_string indent record ^ "." ^ label

let expr_to_string = expr_to_string 0

type texpr =
  | TVar of string * ty
  | TBoolean of bool * ty
  | TNumber of float * ty
  | TIf of texpr * texpr * texpr * ty
    (*TODO: maybe store any metavariables this type captures*)
  | TLet of tpattern * texpr * texpr * ty
  | TLambda of tpattern * texpr * ty
  | TApplication of texpr * texpr * ty
  | TPoly of MetaVariables.t * texpr
  | TTuple of texpr * texpr * ty
  | TRecord of texpr Row.t * ty
  | TRecordAcces of texpr * string * ty

let rec type_of expr =
  match expr with
  | TVar (_, ty)
  | TBoolean (_, ty)
  | TNumber (_, ty)
  | TIf (_, _, _, ty)
  | TLet (_, _, _, ty)
  | TLambda (_, _, ty)
  | TRecordAcces (_, _, ty)
  | TApplication (_, _, ty)
  | TRecord (_, ty)
  | TTuple (_, _, ty) ->
      ty
  | TPoly (metas, expr) -> TPoly (metas, type_of expr)

let rec texpr_to_string indent =
  let next_level = indent + 1 in
  let indent_string = String.make (next_level * 2) ' ' in
  function
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
  | TLet (var, e1, e2, _) ->
      "let " ^ tpattern_to_string var ^ " = ( " ^ texpr_to_string indent e1
      ^ " )\n" ^ indent_string ^ "in ( "
      ^ texpr_to_string next_level e2
      ^ " )"
  | TLambda (var, abs, _) ->
      "\\" ^ tpattern_to_string var ^ ".( " ^ texpr_to_string indent abs ^ " )"
  | TApplication (abs, arg, _) ->
      "( " ^ texpr_to_string indent abs ^ " ) ( " ^ texpr_to_string indent arg
  | TPoly (_, e) -> texpr_to_string indent e
  | TTuple (e1, e2, _) ->
      "( " ^ texpr_to_string indent e1 ^ " , " ^ texpr_to_string indent e2
      ^ " )"
  | TRecord (row, _ty) ->
      "{\n"
      ^ (Row.to_list row
        |> List.map (fun (label, pat) ->
               indent_string ^ label ^ " = " ^ texpr_to_string next_level pat)
        |> String.concat ";\n")
      ^ "\n}"
  | TRecordAcces (record, label, _ty) ->
      texpr_to_string indent record ^ "." ^ label

let texpr_to_string = texpr_to_string 0

type 'a programF = Bind of string * 'a | Expr of 'a

let program_to_string = function
  | Bind (name, expr) -> name ^ " = " ^ expr_to_string expr
  | Expr expr -> expr_to_string expr

let tprogram_to_string = function
  | Bind (name, expr) ->
      name ^ ": "
      ^ (expr |> type_of |> type_to_string)
      ^ " = " ^ texpr_to_string expr
  | Expr expr -> texpr_to_string expr

type program = expr programF
type tprogram = texpr programF
