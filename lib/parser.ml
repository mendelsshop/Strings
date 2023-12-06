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

let octal_digit = sat (fun o -> '0' <= o && o <= '7')

let escaped =
  let slash = char '\\' in
  let quote = char '\"' in
  let newline = char 'n' <$> fun _ -> '\n' in
  let carriage = char 'r' <$> fun _ -> '\r' in
  let form_feed = char 'f' <$> fun _ -> '\x0c' in
  let bell = char 'a' <$> fun _ -> '\x08' in
  let backspace = char 'b' <$> fun _ -> '\b' in
  let tab = char 't' <$> fun _ -> '\t' in
  let vertical_tab = char 'v' <$> fun _ -> '\x09' in
  let null = char '0' <$> fun _ -> '\x00' in
  let octal =
    count 3 octal_digit <$> fun o ->
    "0o" ^ implode o |> int_of_string |> char_of_int
  in
  let hex2 =
    char 'x' << count 2 alphanum <$> fun x ->
    "0x" ^ implode x |> int_of_string |> char_of_int
  in
  let hex4 =
    char 'u' << count 4 alphanum <$> fun x ->
    "0x" ^ implode x |> int_of_string |> char_of_int
  in
  let hex8 =
    char 'U' << count 8 alphanum <$> fun x ->
    "0x" ^ implode x |> int_of_string |> char_of_int
  in
  char '\\'
  << choice
       [
         slash;
         quote;
         newline;
         carriage;
         form_feed;
         bell;
         backspace;
         tab;
         vertical_tab;
         null;
         octal;
         hex2;
         hex4;
         hex8;
       ]

let string_of_char = String.make 1

let string_parser =
  seq (opt escaped) (sat (fun c -> c != '\"')) <$> fun (esc, str) ->
  Option.fold ~none:(str :: []) ~some:(fun esc -> [ esc; str ]) esc

let string_parser =
  many string_parser <$> fun ss -> implode (List.concat_map Fun.id ss)

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
