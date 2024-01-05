open Strings.Parser

let () =
  let open Alcotest in
  let parse_result =
    string_parser [ 'f'; 'o'; 'o' ] |> function
    | Some (Strings.Ast.String s, []) -> Some s
    | _ -> Some ""
  in
  let actual = Some "foo" in
  run "Parsers"
    [
      ( "unquoted strings",
        [
          test_case "foo" `Quick (fun () ->
              Alcotest.(check (option string)) "string foo" actual parse_result);
        ] );
    ]
