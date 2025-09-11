open Strings
open Infer

let read_to_string file = open_in file |> Stdio.In_channel.input_all

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

  let parsed = Parser.run Parser.parse input in
  Result.fold ~error:Fun.id
    ~ok:(fun exprs ->
      Ast.program_to_string exprs |> print_endline;
      let exprs = Strings.Ast2.ast_to_ast2 exprs in
      let exprs' = infer exprs in
      Typed_ast.program_to_string exprs'
      (*               Strings.Eval.eval typed Strings.Eval.env |> fst; *))
    parsed
  |> print_endline
