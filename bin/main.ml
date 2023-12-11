let () =
  let input = read_line () in
  let parsed = Strings.Parser.parser (List.of_seq (String.to_seq input)) in
  Option.value ~default:"bad type"
    (Option.map
       (fun (t, _) ->
         Strings.Ast.list_to_string
           (List.map
              (fun x ->
                x |> Strings.Ast2.ast_to_ast2 |> Strings.Ast2.ast_to_string)
              t))
       parsed)
  |> print_endline
