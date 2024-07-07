module MetaVariables = Set.Make (String)

type ty =
  | TInt
  | TBool
  | TArrow of ty * ty
  | TMeta of string
  | TPoly of MetaVariables.t * ty

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
  | Let of string * expr * expr
  | Lambda of string * expr
  | Application of expr * expr

type texpr =
  | TVar of string * ty
  | TBoolean of bool * ty
  | TNumber of float * ty
  | TIf of texpr * texpr * texpr * ty
  | TLet of string * texpr * texpr * ty
  | TLambda of string * ty * texpr * ty
  | TApplication of texpr * texpr * ty
  | TPoly of MetaVariables.t * texpr

let rec type_of expr =
  match expr with
  | TVar (_, ty)
  | TBoolean (_, ty)
  | TNumber (_, ty)
  | TIf (_, _, _, ty)
  | TLet (_, _, _, ty)
  | TLambda (_, _, _, ty)
  | TApplication (_, _, ty) ->
      ty
  | TPoly (metas, expr) -> TPoly (metas, type_of expr)
