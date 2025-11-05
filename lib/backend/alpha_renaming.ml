open Typed_ast
open Utils
module StringEnv = Env.Make (String)

let gensym' i =
  let n = gensym_int () in
  i ^ string_of_int n

let rec alpha_rename_pattern = function
  | PTVar ({ ident; _ } as p) ->
      let ident' = gensym' ident in
      (StringEnv.singleton ident ident', PTVar { p with ident = ident' })
  | ( PTUnit _ | PTWildcard _ | PTInteger _ | PTFloat _ | PTBoolean _
    | PTString _ ) as p ->
      (StringEnv.empty, p)
  | PTAs ({ name; value; _ } as p) ->
      let name' = gensym' name in
      let env, value = alpha_rename_pattern value in
      (StringEnv.add name name' env, PTAs { p with name = name'; value })
  | PTConstructor ({ value; _ } as p) ->
      let env, value = alpha_rename_pattern value in
      (env, PTConstructor { p with value })
  | PTNominalConstructor ({ value; _ } as p) ->
      let env, value = alpha_rename_pattern value in
      (env, PTNominalConstructor { p with value })
  | PTRecord ({ fields; _ } as p) ->
      let env, fields =
        List.fold_left_map
          (fun env { value; label } ->
            let env', value = alpha_rename_pattern value in
            (StringEnv.union env env', { value; label }))
          StringEnv.empty fields
      in
      (env, PTRecord { p with fields })
  | PTOr ({ patterns; _ } as p) ->
      let env, patterns =
        List.fold_left_map
          (fun env value ->
            let env', value = alpha_rename_pattern value in
            (StringEnv.union env env', value))
          StringEnv.empty patterns
      in
      (env, PTOr { p with patterns })

let rec alpha_rename_expr env = function
  | TVar ({ ident; _ } as e) -> TVar { e with ident = StringEnv.find ident env }
  | (TFloat _ | TString _ | TInteger _ | TBoolean _ | TUnit _) as e -> e
  | TLambda { parameter; parameter_ty; body; ty; span } ->
      let env', parameter = alpha_rename_pattern parameter in
      let body = alpha_rename_expr (StringEnv.union env' env) body in
      TLambda { parameter; parameter_ty; body; ty; span }
  | TApplication { lambda; arguement; ty; span } ->
      let lambda = alpha_rename_expr env lambda in
      let arguement = alpha_rename_expr env arguement in
      TApplication { lambda; arguement; ty; span }
  | TLet { name; name_ty; e1; e2; ty; span } ->
      let env', name = alpha_rename_pattern name in
      let e1 = alpha_rename_expr env e1 in
      let e2 = alpha_rename_expr (StringEnv.union env' env) e2 in
      TLet { name; name_ty; e1; e2; ty; span }
  | TLetRec { name; name_ty; e1; e2; ty; span } ->
      let env', name = alpha_rename_pattern name in
      let e1 = alpha_rename_expr (StringEnv.union env' env) e1 in
      let e2 = alpha_rename_expr (StringEnv.union env' env) e2 in
      TLetRec { name; name_ty; e1; e2; ty; span }
  | TIf { condition; consequent; alternative; ty; span } ->
      let condition = alpha_rename_expr env condition in
      let consequent = alpha_rename_expr env consequent in
      let alternative = alpha_rename_expr env alternative in
      TIf { condition; consequent; alternative; ty; span }
  | TRecordAccess { record; projector; ty; span } ->
      let record = alpha_rename_expr env record in
      TRecordAccess { record; projector; ty; span }
  | TRecordExtend { record; new_fields; ty; span } ->
      let record = alpha_rename_expr env record in
      let new_fields =
        List.map
          (fun { label; value } ->
            let value = alpha_rename_expr env value in

            { value; label })
          new_fields
      in
      TRecordExtend { record; new_fields; ty; span }
  | TRecord { fields; ty; span } ->
      let fields =
        List.map
          (fun { label; value } ->
            let value = alpha_rename_expr env value in

            { value; label })
          fields
      in
      TRecord { fields; ty; span }
  | TMatch { value; cases; ty; span } ->
      let value = alpha_rename_expr env value in
      let cases =
        List.map
          (fun { Ast.pattern; result } ->
            let result = alpha_rename_expr env result in

            { Ast.pattern; result })
          cases
      in
      TMatch { value; cases; ty; span }
  | TConstructor { name; value; ty; span } ->
      let value = alpha_rename_expr env value in
      TConstructor { name; value; ty; span }
  | TNominalConstructor { name; value; ty; span; id } ->
      let value = alpha_rename_expr env value in
      TNominalConstructor { name; value; ty; span; id }

let alpha_rename_tl env = function
  | TBind { name; name_ty; value; span } ->
      let value = alpha_rename_expr env value in
      let env', name = alpha_rename_pattern name in

      (StringEnv.union env' env, TBind { name; name_ty; value; span })
  | TRecBind { name; name_ty; value; span } ->
      let env', name = alpha_rename_pattern name in
      let env = StringEnv.union env' env in
      let value = alpha_rename_expr env value in
      (env, TRecBind { name; name_ty; value; span })
  | TExpr expr ->
      let expr = alpha_rename_expr env expr in
      (env, TExpr expr)
  | TPrintString s -> (env, TPrintString s)

let alpha_rename_tls env tls = List.fold_left_map alpha_rename_tl env tls |> snd
