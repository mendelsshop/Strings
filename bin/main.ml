let rec print_type ty =
  let open Strings.Ast in
  match ty with
  | WildCard -> "_"
  | TypeIdent t -> t
  | Function (t1, t2) -> "(" ^ print_type t1 ^ ") -> (" ^ print_type t2 ^ ")"

let () =
  let input = read_line () in
  let type_parsed =
    Strings.Parser.type_parser (List.of_seq (String.to_seq input))
  in
  Option.value ~default:"bad type"
    (Option.map (fun (t, _) -> print_type t) type_parsed)
  |> print_endline
