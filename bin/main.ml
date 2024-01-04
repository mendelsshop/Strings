(* let () = *)
(*   let input = read_line () in *)
(*   let parsed = Strings.Parser.parser (List.of_seq (String.to_seq input)) in *)
(*   Option.value ~default:"bad type" *)
(*     (Option.map *)
(*        (fun (t, _) -> *)
(*          Strings.Ast.list_to_string *)
(*            (List.map *)
(*               (fun x -> *)
(*                 let typed = *)
(*                   fst *)
(*                     (Option.get *)
(*                        (Strings.Type_checker.typify *)
(*                           (x |> Strings.Ast2.ast_to_ast2) *)
(*                           [])) *)
(*                 in *)
(*                 Strings.Typed_ast.ast_to_string typed *)
(*                 ^ "\n" *)
(*                 ^ Strings.Type_checker.print_constraints *)
(*                     (Strings.Type_checker.generate_constraints typed)) *)
(*               t)) *)
(*        parsed) *)
(*   |> print_endline *)
let () =
  let input = read_line () in
  let parsed = Strings.Parser.parser (List.of_seq (String.to_seq input)) in
  Option.value ~default:"bad type"
    (Option.map
       (fun (t, _) ->
         Strings.Ast.list_to_string
           (List.map
              (fun x ->
                let infered, (ctx, _) =
                  Option.get
                    (Strings.Type_checker.infer
                       (Strings.Ast2.ast_to_ast2 x)
                       ([], 0))
                in
                Strings.Typed_ast.ast_to_string infered
                ^ "\n"
                ^ Strings.Ast.list_to_string
                    (List.map
                       (fun (i, ty) ->
                         i ^ ": " ^ Strings.Typed_ast.type_to_string ty)
                       ctx))
              t))
       parsed)
  |> print_endline
