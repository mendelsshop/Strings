open Strings.Parser
open Strings.Ast
open Alcotest

let pattern =
  let pp f t = Fmt.pf f "@[default=%s]" (pattern_to_string t) in
  let equal = ( = ) in
  Alcotest.testable pp equal

let ast =
  let pp f t = Fmt.pf f "@[default=%s]" (expr_to_string t) in
  let equal = ( = ) in
  Alcotest.testable pp equal

let junk =
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
    ] )

let pattern =
  let unit_ok =
    Strings.Parser.run (Strings.Parser.unit (fun _ _ -> ())) "  ( \n )"
    |> Result.to_option
  in
  let actual_unit_ok = Some () in
  let quoted_string =
    Strings.Parser.run Strings.Parser.pattern " \"avc\"" |> Result.to_option
  in
  let actual_quoted_string =
    Some (PString { value = "avc"; span = { start = 0; finish = 0 } })
  in
  let wildcard =
    Strings.Parser.run Strings.Parser.pattern "_" |> Result.to_option
  in
  let actual_wildcard = Some (PWildcard { start = 0; finish = 0 }) in
  (*   let constructor = *)
  (*   Strings.Parser.run Strings.Parser.pattern "`foobar (5.5, \"baz\")" *)
  (*   |> Result.to_option *)
  (* in *)
  (* let actual_constructor = *)
  (*   Some *)
  (*     (PConstructor *)
  (*        { name = "foobar"; value = PTuple [ PFloat 5.5; PString "baz" ] }) *)
  (* in *)
  let record =
    Strings.Parser.run Strings.Parser.pattern " { ( >> ) = 5; lag = \"baz\" }"
    |> Result.to_option
  in
  let actual_record =
    Some
      (PRecord
         {
           fields =
             [
               {
                 label = ">>";
                 value =
                   PInteger { value = 5; span = { start = 0; finish = 0 } };
               };
               {
                 label = "lag";
                 value =
                   PString { value = "baz"; span = { start = 0; finish = 0 } };
               };
             ];
           span = { start = 0; finish = 0 };
         })
  in
  ( "patterns",
    [
      test_case "unit_ok" `Quick (fun () ->
          Alcotest.(check (option unit)) "unit" actual_unit_ok unit_ok);
      test_case "string" `Quick (fun () ->
          Alcotest.(check (option pattern))
            "string" actual_quoted_string quoted_string);
      test_case "wildcard" `Quick (fun () ->
          Alcotest.(check (option pattern)) "wildcard" actual_wildcard wildcard);
      (* test_case "constructor" `Quick (fun () -> *)
      (*     Alcotest.(check (option pattern)) *)
      (*       "constructor" actual_constructor constructor); *)
      test_case "record" `Quick (fun () ->
          Alcotest.(check (option pattern)) "record" actual_record record);
    ] )

let expression =
  let application =
    Strings.Parser.run (Strings.Parser.expr true) "foo  \"abc\" 4.4\"\n"
    |> Result.map_error (fun e ->
        print_endline e;
        e)
    |> Result.to_option
  in
  let actual_application =
    Some
      (Application
         {
           lambda =
             Application
               {
                 lambda =
                   Var { ident = "foo"; span = { start = 0; finish = 0 } };
                 arguement =
                   String { value = "abc"; span = { start = 0; finish = 0 } };
                 span = { start = 0; finish = 0 };
               };
           arguement = Float { value = 4.4; span = { start = 0; finish = 0 } };
           span = { start = 0; finish = 0 };
         })
  in
  ( "expressions",
    [
      test_case "application" `Quick (fun () ->
          Alcotest.(check (option ast))
            "application" actual_application application);
    ] )

let () = run "Parsers" [ junk; pattern; expression ]
