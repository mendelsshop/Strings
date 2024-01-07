(* let () = *)
(*   let input = read_line () in *)
(*   let parsed = Strings.Parser.parser (List.of_seq (String.to_seq input)) in *)
(*   Option.value ~default:"bad type" *)
(*     (Option.map *)
(*        (fun (t, _) -> *)
(*          Strings.Ast.list_to_string *)
(*            (List.map *)
(*               (fun x -> *)
(*                 let typed = *)
(*                   fst *)
(*                     (Option.get *)
(*                        (Strings.Type_checker.typify *)
(*                           (x |> Strings.Ast2.ast_to_ast2) *)
(*                           [])) *)
(*                 in *)
(*                 Strings.Typed_ast.ast_to_string typed *)
(*                 ^ "\n" *)
(*                 ^ Strings.Type_checker.print_constraints *)
(*                     (Strings.Type_checker.generate_constraints typed)) *)
(*               t)) *)
(*        parsed) *)
(*   |> print_endline *)
let () =
  let input = read_line () in
  let parsed = Strings.Parser.run Strings.Parser.parser input in
  Option.value ~default:"not parsed"
    (Option.map
       (fun t ->
         List.fold_left
           (fun ((ctx, i), str) x ->
             let infered, (ctx', i') =
               Option.get
                 (Strings.Type_checker.infer
                    (Strings.Ast2.ast_to_ast2 x)
                    (ctx, i))
             in
             ((ctx', i'), str ^ Strings.Typed_ast.ast_to_string infered ^ "\n"))
           (([], 0), "")
           t
         |> snd)
       parsed)
  |> print_string
