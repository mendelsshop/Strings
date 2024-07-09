open AMPCL
open Expr

let ( << ) f g x = f (g x)

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

let ident_parser = ident <$> fun i -> Var i

let lambda_parser expr =
  char '\\' >>= fun _ ->
  ident >>= fun ident ->
  char '.' >>= fun _ ->
  expr <$> fun expr -> Lambda (ident, expr)

let rec application_parser expr =
  application_parser expr >>= fun abs ->
  opt expr <$> function Some arg -> Application (abs, arg) | None -> abs

let if_parser expr =
  string "if" >>= fun _ ->
  expr >>= fun cond ->
  string "then" >>= fun _ ->
  expr >>= fun cons ->
  string "else" >>= fun _ ->
  expr <$> fun alt -> If (cond, cons, alt)

let let_parser expr =
  string "let" >>= fun _ ->
  ident >>= fun ident ->
  expr >>= fun e1 ->
  string "in" >>= fun _ ->
  expr <$> fun e2 -> Let (ident, e1, e2)

let parens_parser expr =
  char '(' >>= fun _ ->
  expr >>= fun expr ->
  char ')' <$> fun _ -> expr

let rec expr input =
  choice
    [
      parens_parser expr;
      boolean_parser;
      number_parser;
      ident_parser;
      application_parser expr;
      lambda_parser expr;
      let_parser expr;
      if_parser expr;
    ]
    input
