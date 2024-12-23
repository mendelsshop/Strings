module Unit = struct
  include Unit

  let show _ = ""
end

module Parser = AMPCL.Parser.Char.String.Show.Make (Unit)
open Parser

(* function composition *)
let ( & ) f g x = f (g x)

(* function wise or - takes two functions that return boolean and ors when given an input *)
let ( |-> ) f g x = f x || g x

(* function wise and - takes two functions that return boolean and ands when given an input *)
let ( &-> ) f g x = f x && g x

(* function wise not - takes a function that returns a boolean and nots it when given an input *)
let ( !-> ) f = not & f

let keywords =
  [ "fun"; "let"; "rec"; "in"; "if"; "then"; "else"; "match"; "with" ]

let reserved_operators = [ "->"; "." ]
let is_white_space = Fun.flip List.mem [ ' '; '\t'; '\n' ]
let is_lower_case_letter = ( <= ) 'a' &-> ( >= ) 'z'
let is_upper_case_letter = ( <= ) 'A' &-> ( >= ) 'Z'
let is_letter = is_upper_case_letter |-> is_lower_case_letter
let is_octal = ( <= ) '0' &-> ( >= ) '7'
let is_decimal = is_octal |-> (( = ) '8' &-> ( = ) '9')
let is_hexadecimal = is_decimal |-> is_letter
let string_of_char = String.make 1
let is_in list x = List.mem x list
let not_in list x = not (List.mem x list)

let line_comment =
  between (string "--")
    (char '\n' |> opt)
    (takeWhile (( <> ) '\n' |-> ( <> ) '\"'))
  <?> "comment"

let multi_line_comment =
  between (char '#') (char '#') (takeWhile (( <> ) '#')) <?> "comment"

let white_space = takeWhile is_white_space
let comment = line_comment <|> multi_line_comment
let junk = many (comment <|> white_space)

let basic_identifier =
  junk << letter <$> string_of_char >>= fun first ->
  takeWhile is_hexadecimal <$> ( ^ ) first
  |> check (not_in keywords)
  <?> "identifier"

let infix_identifier =
  let not_infix_symbols =
    is_hexadecimal
    |-> (Fun.flip List.mem) [ '('; ')'; '['; ']'; '\"'; '{'; '}' ]
  in
  let infix_symbols = !->not_infix_symbols in
  junk << sat infix_symbols <$> string_of_char >>= fun start ->
  takeWhile infix_symbols <$> ( ^ ) start
  |> check (not_in reserved_operators)
  <?> "infix identifier"

let identifier =
  basic_identifier
  <|> (* TODO: junk/comments *)
  between (junk << char '(') (junk << char ')') infix_identifier

let number_inner = takeWhile is_decimal
let number1_inner = check (( > ) 0 & String.length) (takeWhile is_decimal)
let number = junk << number1_inner <$> int_of_string <?> "number"

let float =
  junk
  << (number1_inner
     >>= (fun first -> char '.' << number_inner <$> ( ^ ) (first ^ "."))
     <|> ( number_inner >>= fun first ->
           char '.' << number1_inner <$> ( ^ ) (first ^ ".") ))
  <$> float_of_string <?> "float"

let unit : unit t =
  junk << char '(' << junk << char ')' <$> Fun.const () <?> "unit"

let paren = between (junk << char '(') (junk << char ')')
let tuple = Fun.flip sepby1 (junk << char ',')

let record p identifier_short_hand assign =
  let field = seq identifier (junk << char assign << p) in
  let field =
    match identifier_short_hand with
    | Some f -> field <|> (identifier <$> fun field -> (field, f field))
    | None -> field
  in
  between (junk << char '{') (junk << char '}') (sepby field (junk << char ';'))

(* variant parser is only used for types so it won't be ambiguous with application parser *)
let variant p =
  opt (junk << char '|') << seq identifier p >>= fun first ->
  many (junk << char '|' << seq identifier p) <$> List.cons first

let constructor = seq identifier
let typeP = failwith "TODO: type parsing"
let ascription = Fun.flip seq (junk << char ':' << typeP)
