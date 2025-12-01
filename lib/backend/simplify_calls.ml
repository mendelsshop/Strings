open Typed_ast

let rec expand_cond_app k = function
  | TIf ({ consequent : 't texpr; alternative : 't texpr; _ } as i) ->
      TIf
        {
          i with
          consequent = expand_cond_app k consequent;
          alternative = expand_cond_app k alternative;
        }
  | TMatch ({ cases; _ } as m) ->
      let cases =
        List.map
          (fun { Ast.pattern; result } ->
            { Ast.pattern; result = expand_cond_app k result })
          cases
      in
      TMatch { m with cases }
  | t -> k t

type 'a state = [ `None | `Lambda of 'a -> 'a | `Cond of 'a -> 'a ]

let apply_k default = function
  | `None | `Lambda _ -> (default, false)
  | `Cond f ->
      let ty = type_of_expr default in
      if Types.is_function ty then (f default, true) else (default, false)

let upgrade = function `Lambda f -> `Cond f | default -> default

let rec simplify k = function
  | (TVar _ | TFloat _ | TString _ | TInteger _ | TBoolean _ | TUnit _) as t ->
      apply_k t k
  | TApplication ({ lambda; arguement; _ } as w) ->
      let arguement', inlined =
        simplify
          (match k with
          | `None ->
              `Lambda
                (fun inner_lambda ->
                  let lambda', _ =
                    simplify
                      (`Lambda
                         (fun lambda ->
                           TApplication
                             { w with arguement = inner_lambda; lambda }))
                      lambda
                  in
                  lambda')
          | `Cond f ->
              `Cond
                (fun inner_lambda ->
                  let lambda', _ =
                    simplify
                      (`Cond
                         (fun lambda ->
                           f
                             (TApplication
                                { w with arguement = inner_lambda; lambda })))
                      lambda
                  in
                  lambda')
          | `Lambda f ->
              `Lambda
                (fun inner_lambda ->
                  let lambda', _ =
                    simplify
                      (`Lambda
                         (fun lambda ->
                           f
                             (TApplication
                                { w with arguement = inner_lambda; lambda })))
                      lambda
                  in
                  lambda'))
          arguement
      in
      if inlined then (arguement', true)
      else
        let lambda', inlined =
          simplify
            (match k with
            | `Lambda f ->
                `Lambda
                  (fun lambda ->
                    f (TApplication { w with arguement = arguement'; lambda }))
            | `Cond f ->
                `Cond
                  (fun lambda ->
                    f (TApplication { w with arguement = arguement'; lambda }))
            | `None ->
                `Lambda
                  (fun lambda ->
                    TApplication { w with arguement = arguement'; lambda }))
            lambda
        in
        if inlined then (lambda', inlined)
        (* potential bug if most inner application arguement is if but none of the outer applicaations is in which case we shouldn't do anything i think *)
        (* but right now it just straight of removes the arguement for some reason *)
        (* we mostly prevent it by checking that the thing passed into k is actually a function, but doesn't work if last arguement is a function (when you have hof) *)
          else
          apply_k
            (TApplication { w with arguement = arguement'; lambda = lambda' })
            k
  | TLambda ({ body; _ } as l) ->
      apply_k (TLambda { l with body = simplify `None body |> fst }) k
  | TLetRec ({ e1; e2; _ } as l) ->
      let e1, _ = simplify `None e1 in
      let e2, inlined = simplify k e2 in
      (TLetRec { l with e1; e2 }, inlined)
  | TLet ({ e1; e2; _ } as l) ->
      let e1, _ = simplify `None e1 in
      let e2, inlined = simplify k e2 in
      (TLet { l with e1; e2 }, inlined)
  | TIf ({ condition; consequent; alternative; _ } as i) ->
      let consequent, inlined = simplify (upgrade k) consequent in
      let alternative, inlined' = simplify (upgrade k) alternative in
      ( TIf
          {
            i with
            condition = simplify `None condition |> fst;
            consequent;
            alternative;
          },
        inlined || inlined' )
  | TMatch ({ cases; value; _ } as m) ->
      let value, _ = simplify `None value in
      let inlined, cases =
        List.fold_left_map
          (fun inline { Ast.pattern; result } ->
            let result, inline' = simplify (upgrade k) result in
            (inline || inline', { Ast.pattern; result }))
          false cases
      in
      (TMatch { m with value; cases }, inlined)
  | TRecordAccess ({ record; _ } as r) ->
      apply_k (TRecordAccess { r with record = simplify `None record |> fst }) k
  | TRecordExtend ({ record; new_fields; _ } as r) ->
      apply_k
        (TRecordExtend
           {
             r with
             record = simplify `None record |> fst;
             new_fields =
               List.map
                 (fun { Utils.label; value } ->
                   { Utils.label; value = simplify `None value |> fst })
                 new_fields;
           })
        k
  | TRecord ({ fields; _ } as r) ->
      apply_k
        (TRecord
           {
             r with
             fields =
               List.map
                 (fun { Utils.label; value } ->
                   { Utils.label; value = simplify `None value |> fst })
                 fields;
           })
        k
  | TConstructor ({ value; _ } as c) ->
      (* we could simplify constructors, but that would mean we would also need `Constructor *)
      let value, _ = simplify k value in
      apply_k (TConstructor { c with value }) k
  | TNominalConstructor ({ value; _ } as c) ->
      (* nominal constructors are always behind a lambda like (\x. Con x) so no point in simplifing unless we inlined the function in some cases *)
      let value, _ = simplify k value in
      apply_k (TNominalConstructor { c with value }) k

let simplify e = simplify `None e

let simplify_tl = function
  | TBind ({ value; _ } as b) -> TBind { b with value = simplify value |> fst }
  | TRecBind ({ value; _ } as b) ->
      TRecBind { b with value = simplify value |> fst }
  | TPrintString _ as p -> p
  | TExpr value -> TExpr (simplify value |> fst)

let simplify_tls tls = List.map simplify_tl tls
