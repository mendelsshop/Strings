open Strings.Parser

let pattern =
  let pp f t = Fmt.pf f "@[default=%s]" (Strings.Ast.pattern_to_string t) in
  let equal = ( = ) in
  Alcotest.testable pp equal

let () =
  let open Alcotest in
  let comment_mutli_line =
    Strings.Parser.run comment "#fff#kf" |> Result.to_option
  in
  let actual_comment_multi_line = Some "fff" in
  let bad_comment_mutli_line =
    Strings.Parser.run comment "#fff" |> function Ok s -> Some s | _ -> None
  in
  let bad_actual_comment_multi_line = None in

  let comment_single_line =
    Strings.Parser.run comment "--abc\n" |> Result.to_option
  in
  let actual_comment_single_line = Some "abc" in
  let white_space =
    Strings.Parser.run white_space "  \n\t--abc" |> Result.to_option
  in
  let actual_white_space = Some "  \n\t" in
  let has_junk =
    Strings.Parser.run junk "#sff\n# \t--fff \n\t\t --abc\n   "
    |> Result.to_option
  in
  let actual_has_junk =
    Some [ "sff\n"; " \t"; "fff "; "\t\t "; "abc"; "   " ]
  in
  let unit_ok =
    Strings.Parser.run Strings.Parser.unit "  ( \n )" |> Result.to_option
  in
  let actual_unit_ok = Some () in
  let quoted_string =
    Strings.Parser.run Strings.Parser.pattern " \"avc\"" |> Result.to_option
  in
  let actual_quoted_string = Some (Strings.Ast.PString "avc") in
  let wildcard =
    Strings.Parser.run Strings.Parser.pattern "_" |> Result.to_option
  in
  let actual_wildcard = Some Strings.Ast.PWildCard in
  run "Parsers"
    [
      ( "junk",
        [
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
      ( "patterns",
        [
          test_case "unit_ok" `Quick (fun () ->
              Alcotest.(check (option unit)) "unit" actual_unit_ok unit_ok);
          test_case "string" `Quick (fun () ->
              Alcotest.(check (option pattern))
                "string" actual_quoted_string quoted_string);
          test_case "wildcard" `Quick (fun () ->
              Alcotest.(check (option pattern))
                "wildcard" actual_wildcard wildcard);
        ] );
      ("expressions", []);
    ]
