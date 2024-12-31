open Strings.Parser

let () =
  let open Alcotest in
  let comment_mutli_line =
    Strings.Parser.run multi_line_comment "#fff#" |> function
    | Ok s -> Some s
    | _ -> None
  in
  let actual_comment_multi_line = Some "fff" in
  let bad_comment_mutli_line =
    Strings.Parser.run multi_line_comment "#fff" |> function
    | Ok s -> Some s
    | _ -> None
  in
  let bad_actual_comment_multi_line = None in

  let comment_single_line =
    Strings.Parser.run line_comment "--abc" |> function
    | Ok s -> Some s
    | _ -> None
  in
  let actual_comment_single_line = Some "abc" in
  let white_space =
    Strings.Parser.run white_space "  \nt\t--abc" |> function
    | Ok s -> Some s
    | _ -> None
  in
  let actual_white_space = Some "  \n\t" in
  let has_junk =
    Strings.Parser.run junk "  \nt\t--abc" |> function
    | Ok s -> Some s
    | _ -> None
  in
  let actual_has_junk = Some [ "  \n\t"; "abc" ] in
  let unit_ok =
    Strings.Parser.run Strings.Parser.unit "()" |> function
    | Ok s -> Some s
    | _ -> None
  in
  let actual_unit_ok = Some () in
  run "Parsers"
    [
      ( "junk",
        [
          (* test_case "unit_ok" `Quick (fun () -> *)
          (*     Alcotest.(check (option unit)) "string foo" actual_unit_ok unit_ok); *)
          test_case "multi line comment" `Quick (fun () ->
              Alcotest.(check (option string))
                "comment" actual_comment_multi_line comment_mutli_line);
          test_case "multi line comment" `Quick (fun () ->
              Alcotest.(check (option string))
                "comment" bad_actual_comment_multi_line bad_comment_mutli_line);
          test_case "single line comment" `Quick (fun () ->
              Alcotest.(check (option string))
                "comment" actual_comment_single_line comment_single_line);
          test_case "white space" `Quick (fun () ->
              Alcotest.(check (option string))
                "white space" actual_white_space white_space);
          test_case "junk" `Quick (fun () ->
              Alcotest.(check (option (list string)))
                "junk" actual_has_junk has_junk);
        ] );
      ( "expressions",
        [
          test_case "unit_ok" `Quick (fun () ->
              Alcotest.(check (option unit)) "unit" actual_unit_ok unit_ok);
        ] );
    ]
