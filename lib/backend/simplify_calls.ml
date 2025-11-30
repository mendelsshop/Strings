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

type 'a state = [ `None | `Lambda of 'a -> 'a | `If of 'a -> 'a ]

let apply_k default = function
  | `None | `Lambda _ -> (default, false)
  | `If f -> (f default, true)

let upgrade = function `Lambda f -> `If f | default -> default

let rec simplify k = function
  | (TVar _ | TFloat _ | TString _ | TInteger _ | TBoolean _ | TUnit _) as t ->
      apply_k t k
  | TApplication ({ lambda; arguement; _ } as w) ->
      (* TODO: might need to also run f when k is `If *)
      let arguement', inlined =
        simplify
          (`Lambda
             (fun inner_lambda ->
               let lambda', _ =
                 simplify
                   (`Lambda
                      (fun lambda ->
                        match k with
                        | `Lambda f ->
                            f
                              (TApplication
                                 { w with arguement = inner_lambda; lambda })
                        | _ ->
                            TApplication
                              { w with arguement = inner_lambda; lambda }))
                   lambda
               in
               lambda'))
          arguement
      in
      if inlined then (arguement', true)
      else
        let lambda', inlined =
          simplify
            (`Lambda
               (fun lambda ->
                 match k with
                 | `Lambda f ->
                     f (TApplication { w with arguement = arguement'; lambda })
                 | _ -> TApplication { w with arguement = arguement'; lambda }))
            lambda
        in
        if inlined then (lambda', inlined)
        else
          ( TApplication { w with arguement = arguement'; lambda = lambda' },
            false )
  | TLambda ({ body; _ } as l) ->
      apply_k (TLambda { l with body = simplify `None body |> fst }) k
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
  | TLetRec _ | TRecordAccess _ | TRecordExtend _ | TRecord _ | TMatch _
  | TConstructor _ | TNominalConstructor _ ->
      failwith ""

let simplify e = simplify `None e

let simplify_tl = function
  | TBind ({ value; _ } as b) -> TBind { b with value = simplify value |> fst }
  | TRecBind ({ value; _ } as b) ->
      TRecBind { b with value = simplify value |> fst }
  | TPrintString _ as p -> p
  | TExpr value -> TExpr (simplify value |> fst)

let simplify_tls tls = List.map simplify_tl tls
