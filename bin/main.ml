let () =
  let input = read_line () in
  let parsed = Strings.Parser.run Strings.Parser.parser input in
  Option.value ~default:"not parsed"
    (Option.map
       (fun t ->
         Strings.Ast2.ast_to_ast2 t |> Strings.Type_checker.infer
         |> Option.fold ~none:"not type checked" ~some:(fun typed ->
                typed |> fst |> Strings.Typed_ast.print_program))
       parsed)
  |> print_endline
