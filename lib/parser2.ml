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
let is_lower_case_letter = ( <= ) 'a' &-> ( >= ) 'z'
let is_upper_case_letter = ( <= ) 'A' &-> ( >= ) 'Z'
let is_letter = is_upper_case_letter |-> is_lower_case_letter
let is_octal = ( <= ) '0' &-> ( >= ) '7'
let is_decimal = is_octal |-> (( = ) '8' &-> ( = ) '9')
let is_hexadecimal = is_decimal |-> is_letter
let string_of_char = String.make 1

let basic_identifier =
  letter <$> string_of_char >>= fun first ->
  takeWhile is_hexadecimal <$> ( ^ ) first <?> "identifier"

let infix_identifier =
  let not_infix_symbols =
    is_hexadecimal
    |-> (Fun.flip List.mem) [ '('; ')'; '['; ']'; '\"'; '{'; '}' ]
  in
  let infix_symbols = !->not_infix_symbols in
  sat infix_symbols <$> string_of_char >>= fun start ->
  takeWhile infix_symbols <$> ( ^ ) start

let identifier =
  basic_identifier
  <|> (* TODO: junk/comments *)
  between (char '(') (char ')') infix_identifier

let number_inner = takeWhile is_decimal
let number1_inner = check (( > ) 0 & String.length) (takeWhile is_decimal)
let number = number1_inner <$> int_of_string <?> "number"

let float =
  number1_inner
  >>= (fun first ->
        char '.' << number_inner <$> fun rest ->
        first ^ "." ^ rest |> float_of_string)
  <|> ( number_inner >>= fun first ->
        char '.' << number1_inner <$> fun rest ->
        first ^ "." ^ rest |> float_of_string )
  <?> "float"

let line_comment =
  between (string "--")
    (char '\n' |> opt)
    (takeWhile (( <> ) '\n' |-> ( <> ) '\"'))

let multi_line_comment = between (char '#') (char '#') (takeWhile (( <> ) '#'))
let comment = line_comment <|> multi_line_comment
