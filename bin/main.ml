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

  let result = Parser.run Parser.parse input in
  Result.fold
    ~error:(fun e () -> print_endline e)
    ~ok:(fun exprs () ->
      let types, constructors = get_type_env exprs in
      let types = TypeEnv.of_list types in
      let constructors = ConstructorEnv.of_list constructors in
      Ast.program_to_string exprs |> print_endline;
      let exprs = Strings.Ast2.ast_to_ast2 exprs in
      let exprs' = infer exprs { types; constructors } in
      Typed_ast.program_to_string exprs' |> print_endline;
      let errors = Pattern_checking.check exprs' in
      print_endline (Pattern_checking.errors_to_string input errors);
      (* TODO: non fail fast letrec checking *)
      Letrec_checking.check_program exprs';
      if not (List.is_empty errors) then
        failwith ("errors: " ^ string_of_int (List.length errors))
      else Strings.Eval.eval exprs' |> fst)
    result ()
