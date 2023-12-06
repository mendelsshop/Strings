open AMPCL

let is_ws x = x = ' ' || x = '\n' || x == '\t'

let skip_garbage =
  let ws = sat is_ws <$> fun c -> String.make 1 c in
  let line_comment =
    seq (char '#') (many (sat (fun x -> x != '\n'))) <$> fun g ->
    implode (fst g :: snd g)
  in
  many (ws <|> line_comment)

let rec type_parser input =
  let basic_type =
    between (skip_garbage << char '(') (skip_garbage << char ')') type_parser
    <|> (skip_garbage << word1 <$> fun ty -> Ast.TypeIdent ty)
    <|> (skip_garbage << char '_' <$> fun _ -> Ast.WildCard)
  and opt_fn = opt (skip_garbage << string "->" << type_parser) in
  let full_parser = seq basic_type opt_fn in
  ( full_parser <$> fun (t1, (opt_t2 : Ast.ty option)) ->
    Option.fold ~none:t1 ~some:(fun t2 -> Ast.Function (t1, t2)) opt_t2 )
    input

let[@warnerror "-unused-value-declaration"] integer =
  many1 digit <$> fun ns -> Int64.of_string (implode ns)

let integer_opt = many digit
let integer = many1 digit
let decimal = char '.'

let[@warnerror "-unused-value-declaration"] number =
  let number_opt_dot_number = seq integer_opt (seq decimal integer)
  and number_dot_number_opt = seq integer (seq decimal integer_opt) in
  number_dot_number_opt <|> number_opt_dot_number
  <$> fun (f, ((_ : char), s)) -> Float.of_string (implode (f @ ('.' :: s)))
