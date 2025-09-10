open Strings
open Infer

(* let () = UExist (Variables.of_list ["a1", "a2"], (UExist (Variables.of_list ["a3", "a4"], (UExist (Variables.of_list ["a5", "a6"], (UExist (Variables.of_list ["a7"], UAnd (UMulti ([TyVar], *)
(* let term = Let ("y", Lambda ("x", Var "x"), App (Var "y", Var "y")) *)
(* let term = *)
(*   Let *)
(*     ( PVar "y", *)
(*       Lambda (PVar "x", Var "x"), *)
(*       App *)
(*         ( App *)
(*             ( Lambda (PVar "x", Lambda (PVar "x", Var "x")), *)
(*               App (App (Var "y", Var "y"), Unit) ), *)
(*           App (App (Var "y", Var "y"), Number 0.1) ) ) *)
(**)
(* let term = Let ("y", Lambda ("x", App (Var "x", Unit)), App (Var "y", Var "y")) *)
(* let term = Let ("y", Lambda ("x", App (Var "x", Unit)), Var "y") *)

(* let term = Let ("y", Lambda ("x", Var "x"), Var "y") *)

(* let term = Lambda ("x", App (App (Var "x", Var "x"), App (Var "x", Unit))) *)
(* let term = Lambda ("x", Var "x") *)

(* let term = *)
(*   Lambda *)
(*     ( "f", *)
(*       App *)
(*         ( Lambda ("x", App (Var "f", App (Var "x", Var "x"))), *)
(*           Lambda ("x", App (Var "f", App (Var "x", Var "x"))) ) ) *)
(* let term = Lambda ("x", App (Var "x", App (Var "x", Unit))) *)

(* let term = Let ("y", Lambda ("x", Var "x"),App( Var "y", Ml2.Unit)) *)
(* let cs, _elab = generate_constraints (Union_find.make (TyVar ("a", 0))) term *)

(* let () = tterm_to_string elab |> print_endline *)
(* let () = constraints_to_string cs |> print_endline *)
(* let () = tterm_to_string _elab |> print_endline *)
(* let () = solve_constraints [] cs *)
(* let () = print_endline "done" *)
(**)
(* let () = subst_to_string subst |> print_endline *)
(* let tterm = apply_subst_tterm subst elab *)
(* let () = tterm_to_string _elab |> print_endline *)
(* let () = constraints_to_string cs |> print_endline *)
let read_to_string file = open_in file |> Stdio.In_channel.input_all
(* >>>>>>> ml/main *)

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
