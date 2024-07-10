open Ml.Expr
open Ml.Parser

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
  let parsed = run parse input in
  Option.fold ~none:"bad file"
    ~some:(fun exprs -> List.map expr_to_string exprs |> String.concat "\n")
    parsed
  |> prerr_endline
