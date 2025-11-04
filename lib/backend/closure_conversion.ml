open Typed_ast
open Types
open Utils

type 't lexpr =
  | LVar of { ident : string; ty : 't; span : AMPCL.span }
  | LLocalVar of { ident : string; ty : 't; span : AMPCL.span }
  | LFloat of { value : float; ty : 't; span : AMPCL.span }
  | LString of { value : string; ty : 't; span : AMPCL.span }
  | LInteger of { value : int; ty : 't; span : AMPCL.span }
  | LBoolean of { value : bool; ty : 't; span : AMPCL.span }
  | LLambda of { name : int; ty : 't; span : AMPCL.span }
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
  body : 't texpr;
  ty : 't;
  span : AMPCL.span;
}

module FunctionEnv = Env.Make (struct
  type t = ty func
end)

type 't functions = ty func StringMap.t

type 't top_level =
  | LBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't texpr;
      span : AMPCL.span;
    }
  | LRecBind of {
      name : 't tpattern;
      name_ty : 't;
      value : 't texpr;
      span : AMPCL.span;
    }
  | LPrintString of string
  | LExpr of 't texpr

let rec closure_convert_expr : ty texpr -> _ = function
  | TVar _ -> failwith ""
  | TFloat _ -> failwith ""
  | TString _ -> failwith ""
  | TInteger _ -> failwith ""
  | TBoolean _ -> failwith ""
  | TLambda _ -> failwith ""
  | TApplication { lambda; arguement; ty; span } ->
      LApplication
        {
          lambda = closure_convert_expr lambda;
          arguement = closure_convert_expr arguement;
          ty;
          span;
        }
  | TUnit _ -> failwith ""
  | TLet _ -> failwith ""
  | TLetRec _ -> failwith ""
  | TIf _ -> failwith ""
  | TRecordAccess _ -> failwith ""
  | TRecordExtend _ -> failwith ""
  | TRecord _ -> failwith ""
  | TMatch _ -> failwith ""
  | TConstructor _ -> failwith ""
  | TNominalConstructor _ -> failwith ""
