let read_to_string file = open_in file |> In_channel.input_all

let () =
  let args = Array.to_list Sys.argv in
  let file =
    match List.nth_opt args 1 with
    | Some file -> file
    | None ->
        print_endline "usage strings [file]";
        exit 1
  in
  let input = read_to_string file in
  let parsed = Strings.Parser.run Strings.Parser.parser input in
  Option.value ~default:"not parsed"
    (Option.map
       (fun t ->
         Strings.Ast2.ast_to_ast2 t |> Strings.Type_checker.infer
         |> Result.fold
              ~error:(fun e -> "not type checked: " ^ e)
              ~ok:(fun typed ->
                let typed = fst typed in
                Strings.Typed_ast.print_program typed |> print_string;
                Strings.Eval.eval typed Strings.Eval.env |> fst;
                "evaled"))
       parsed)
  |> print_endline
