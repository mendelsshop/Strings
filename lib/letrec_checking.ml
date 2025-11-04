open Typed_ast
open Utils

module Env = Env.Make (struct
  type t = texpr
end)

let remove_all vars = Env.filter (fun key _ -> not (List.mem key vars))

let rec get_binders = function
  | PTVar { ident; _ } -> [ ident ]
  | PTString _ -> []
  | PTWildcard _ -> []
  | PTInteger _ -> []
  | PTFloat _ -> []
  | PTBoolean _ -> []
  | PTRecord { fields; _ } ->
      List.concat_map (fun { value; _ } -> get_binders value) fields
  | PTConstructor { value; _ } -> get_binders value
  | PTNominalConstructor { value; _ } -> get_binders value
  | PTAs { name; value; _ } -> name :: get_binders value
  | PTOr { patterns; _ } -> List.concat_map get_binders patterns
  | PTUnit _ -> []

(* we dont autimatically turn letrec exprs into string we do it on demand as in most cases letrec are correct *)
let rec check_expr rec_env : texpr -> _ = function
  | `TVar { ident; _ } ->
      Env.find_opt ident rec_env
      |> Option.fold ~none:() ~some:(fun letrec_string_function ->
          failwith
            ("recursive variable " ^ ident ^ " of " ^ letrec_string_function ()
           ^ " used in illegal postion (must be enclosed in a labmda)."))
  | `TFloat _ -> ()
  | `TString _ -> ()
  | `TInteger _ -> ()
  | `TBoolean _ -> ()
  | `TLambda { body; _ } -> check_expr StringMap.empty body
  | `TApplication { lambda; arguement; _ } ->
      check_expr rec_env lambda;
      check_expr rec_env arguement
  | `TUnit _ -> ()
  | `TLet { e1; e2; name; _ } ->
      check_expr rec_env e1;
      check_expr (remove_all (get_binders name) rec_env) e2
  | `TLetRec { name; e1; e2; _ } as letrec ->
      check_expr
        (Env.union
           (get_binders name
           |> List.map (fun name -> (name, fun () -> texpr_to_string letrec))
           |> Env.of_list)
           rec_env)
        e1;
      check_expr rec_env e2
  | `TIf { condition; consequent; alternative; _ } ->
      check_expr rec_env condition;
      check_expr rec_env consequent;
      check_expr rec_env alternative
  | `TRecordAccess { record; _ } -> check_expr rec_env record
  | `TRecordExtend { new_fields; record; _ } ->
      check_expr rec_env record;
      List.iter (fun { value; _ } -> check_expr rec_env value) new_fields
  | `TRecord { fields; _ } ->
      List.iter (fun { value; _ } -> check_expr rec_env value) fields
  | `TMatch { value; cases; _ } ->
      check_expr rec_env value;
      List.iter
        (fun { Ast.result; pattern } ->
          check_expr (remove_all (get_binders pattern) rec_env) result)
        cases
  | `TConstructor { value; _ } -> check_expr rec_env value
  | `TNominalConstructor { value; _ } -> check_expr rec_env value

let check_top_level = function
  | TBind { value; _ } -> check_expr Env.empty value
  | TRecBind { value; name; _ } as letrec ->
      check_expr
        (get_binders name
        |> List.map (fun name -> (name, fun () -> top_level_to_string letrec))
        |> Env.of_list)
        value
  | _ -> ()

let check_program = List.iter check_top_level
