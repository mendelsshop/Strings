open AMPCL
open Expr

module Unit = struct
  include Unit

  let show _ = ""
end

module Parser = AMPCL.Parser.Char.String.Show.Make (Unit)
open Parser

let key_words =
  [ "match"; "with"; "in"; "let"; "if"; "rec"; "then"; "else"; "\\"; "."; "|" ]

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

let number_parser wrapper =
  many1 digit <$> (float_of_int << int_of_string << implode) <$> wrapper

let boolean_parser wrapper =
  let true_parser = string "true" <$> fun _ -> wrapper true in
  let false_parser = string "false" <$> fun _ -> wrapper false in
  true_parser <|> false_parser

let ident =
  let idents = many alphanum in
  let flatten (f, rest) = f :: rest in
  seq lower idents <$> flatten <$> implode
  |> check (fun x -> not (List.mem x key_words))

let variant_ident =
  let idents = many alphanum in
  let flatten (f, rest) = f :: rest in
  keep_right (char '`')
    (seq letter idents <$> flatten <$> implode
    |> check (fun x -> not (List.mem x key_words)))

let ident_parser wrapper = ident <$> wrapper

let parens_parser expr =
  char '(' >>= fun _ ->
  expr >>= fun expr ->
  !(char ')') <$> fun _ -> expr

(*|> many*)
(*List.fold*)
(*<$> ( List.fold_left wrapper e1)*)
(*function*)
(*| [] -> e1*)
(*| tuples -> wrapper (e1, e2)*)
let record expr =
  (let ( << ) = keep_right in
   let record =
     seq !ident (opt (!(char '=') << expr)) <$> function
     | name, None -> (name, PVar name)
     | name, Some value -> (name, value)
   in
   let record_mid = record >> !(char ';') in
   !(char '{')
   << (many record_mid
      >> !(char '}')
      <|> (seq (many record_mid) record
          <$> (fun (rs, r) -> rs @ [ r ])
          >> !(char '}'))))
  <$> fun r -> PRecord r

let variant_parser wrapper expr =
  seq variant_ident expr <$> fun (name, expr) -> wrapper name expr

let pattern =
  makeRecParser (fun pattern ->
      choice
        [
          parens_parser pattern;
          (char '_' <$> fun _ -> PWildcard);
          ident_parser (fun i -> PVar i);
          number_parser (fun n -> PNumber n);
          boolean_parser (fun b -> PBoolean b);
          record pattern;
          variant_parser (fun name p -> PConstructor (name, p)) pattern;
        ])

let lambda_parser expr =
  char '\\' >>= fun _ ->
  !pattern >>= fun ident ->
  !(char '.') >>= fun _ ->
  expr <$> fun expr -> Lambda (ident, expr)

let if_parser expr =
  string "if" >>= fun _ ->
  expr >>= fun cond ->
  !(string "then") >>= fun _ ->
  expr >>= fun cons ->
  !(string "else") >>= fun _ ->
  expr <$> fun alt -> If (cond, cons, alt)

let record expr =
  (let ( << ) = keep_right in
   let record =
     seq !ident (opt (!(char '=') << expr)) <$> function
     | name, None -> (name, Var name)
     | name, Some value -> (name, value)
   in
   let record_mid = record >> !(char ';') in
   !(char '{')
   << seq
        (expr >> !(string "with") |> opt)
        (many1 record_mid
        >> !(char '}')
        <|> (seq (many record_mid) record
            <$> (fun (rs, r) -> rs @ [ r ])
            >> !(char '}'))))
  <$> function
  | Some init, rows -> RecordExtend (init, rows)
  | None, rows -> Record rows

let let_parser expr =
  string "let" >>= fun _ ->
  opt !(string "rec") >>= fun _rec ->
  !pattern >>= fun ident ->
  !(char '=') >>= fun _ ->
  expr >>= fun e1 ->
  !(string "in") >>= fun _ ->
  expr <$> fun e2 ->
  if Option.is_some _rec then LetRec (ident, e1, e2) else Let (ident, e1, e2)

let record_acces_parser expr =
  expr >>= fun record ->
  many (char '.' >>= fun _ -> ident) <$> fun acceses ->
  List.fold_left
    (fun record field -> RecordAcces (record, field))
    record acceses

let match_parser expr =
  let case = seq pattern (!(string "->") >>= fun _ -> expr) in
  string "match" >>= fun _ ->
  expr >>= fun expr ->
  !(string "with") >>= fun _ ->
  ( seq
      (!(char '|') |> opt >>= fun _ -> case)
      (!(char '|') >>= (fun _ -> case) |> many)
  <$> fun (c, cs) -> c :: cs )
  <$> fun cases -> Match (expr, cases)

let expr =
  makeRecParser (fun expr ->
      let basic_forms =
        makeRecParser (fun basic_forms ->
            !(choice
                [
                  parens_parser expr;
                  boolean_parser (fun b -> Boolean b);
                  number_parser (fun n -> Number n);
                  ident_parser (fun i -> Var i);
                  record expr;
                  variant_parser
                    (fun name p -> Constructor (name, p))
                    basic_forms;
                ]))
      in
      let application_parser =
        makeRecParser (fun application_parser ->
            record_acces_parser basic_forms >>= fun abs ->
            application_parser
            <$> (fun arg -> Application (abs, arg))
            <|> return abs)
      in
      let if_parser =
        makeRecParser (fun ifP -> if_parser ifP <|> application_parser)
      in
      !(choice
          [ if_parser; lambda_parser expr; match_parser expr; let_parser expr ]))

let let_parser =
  string "let" >>= fun _ ->
  opt !(string "rec") >>= fun _rec ->
  !pattern >>= fun ident ->
  !(char '=') >>= fun _ ->
  expr <$> fun e1 ->
  if Option.is_some _rec then RecBind (ident, e1) else Bind (ident, e1)

let top_level = expr <$> (fun e -> Expr e) <|> !let_parser

let parse =
  many1
    ( top_level >>= fun tl ->
      junk <$> fun _ -> tl )
  >> eof

let run = run_show
