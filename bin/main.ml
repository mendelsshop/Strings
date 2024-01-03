let () =
  let input = read_line () in
  let parsed = Strings.Parser.parser (List.of_seq (String.to_seq input)) in
  Option.value ~default:"bad type"
    (Option.map
       (fun (t, _) ->
         Strings.Ast.list_to_string
           (List.map
              (fun x ->
                Strings.Typed_ast.ast_to_string
                  (fst
                     (Option.get
                        (Strings.Type_checker.typify
                           (x |> Strings.Ast2.ast_to_ast2)
                           []))))
              t))
       parsed)
  |> print_endline
