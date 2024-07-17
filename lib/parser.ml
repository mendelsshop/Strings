open AMPCL
open Expr

let key_words = [ "in"; "let"; "if"; "rec"; "then"; "else"; "\\" ]

let junk =
  let non_newline = sat (fun c -> c != '\n') in
  let comment_contents = many non_newline <$> implode in
  let comment =
    string "--" >>= fun comment_start ->
    comment_contents <$> fun contents -> comment_start ^ contents
  in
  let white_space = sat (function ' ' | '\n' | '\t' -> true | _ -> false) in
  let white_spaces = white_space <$> String.make 1 in
  many (white_spaces <|> comment) <$> String.concat ""

let skip_garbage f = junk >>= fun _ -> f
let ( << ) f g x = f (g x)
let ( ! ) = skip_garbage

(*TODO: comments and whitespace*)

let number_parser =
  many1 digit <$> (float_of_int << int_of_string << implode) <$> fun f ->
  Number f

let boolean_parser =
  let true_parser = string "true" <$> fun _ -> Boolean true in
  let false_parser = string "false" <$> fun _ -> Boolean false in
  true_parser <|> false_parser

let ident =
  let idents = many alphanum in
  let flatten (f, rest) = f :: rest in
  seq letter idents <$> flatten <$> implode
  |> check (fun x -> not (List.mem x key_words))

let ident_parser = ident <$> fun i -> Var i

let lambda_parser expr =
  char '\\' >>= fun _ ->
  !ident >>= fun ident ->
  !(char '.') >>= fun _ ->
  expr <$> fun expr -> Lambda (ident, expr)

let if_parser expr =
  string "if" >>= fun _ ->
  expr >>= fun cond ->
  !(string "then") >>= fun _ ->
  expr >>= fun cons ->
  !(string "else") >>= fun _ ->
  expr <$> fun alt -> If (cond, cons, alt)

let let_parser expr =
  string "let" >>= fun _ ->
  !ident >>= fun ident ->
  !(char '=') >>= fun _ ->
  expr >>= fun e1 ->
  !(string "in") >>= fun _ ->
  expr <$> fun e2 -> Let (ident, e1, e2)

let parens_parser expr =
  char '(' >>= fun _ ->
  expr >>= fun expr ->
  !(char ')') <$> fun _ -> expr

let tuple expr =
  expr >>= fun e1 ->
  !(char ',') >>= (fun _ -> expr) |> opt <$> function
  | Some e2 -> Tuple (e1, e2)
  | None -> e1

let rec expr_inner input =
  let basic_forms =
    !(choice
        [
          parens_parser (expr_inner <|> !(let_parser expr_inner));
          boolean_parser;
          number_parser;
          ident_parser;
          lambda_parser expr_inner;
          if_parser expr_inner;
        ])
  in
  let basic_forms = tuple basic_forms in
  let rec application_parser input =
    ( basic_forms >>= fun abs ->
      application_parser <$> (fun arg -> Application (abs, arg)) <|> return abs
    )
      input
  in
  application_parser input

let rec expr input = (expr_inner <|> !(let_parser expr)) input

let let_parser =
  string "let" >>= fun _ ->
  !ident >>= fun ident ->
  !(char '=') >>= fun _ ->
  expr >>= fun e1 -> Bind (ident, e1) |> return

let top_level = expr <$> (fun e -> Expr e) <|> !let_parser

let parse =
  many top_level >>= fun tl ->
  junk <$> fun _ -> tl

let run = run
