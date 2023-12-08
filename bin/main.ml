let () =
  let input = read_line () in
  let parsed = Strings.Parser.parser (List.of_seq (String.to_seq input)) in
  Option.value ~default:"bad type"
    (Option.map
       (fun (t, _) ->
         let _ = List.map Strings.Ast2.ast_to_ast2 t in
         "")
       parsed)
  |> print_endline
