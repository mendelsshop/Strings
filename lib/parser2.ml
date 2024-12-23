module Unit = struct
  include Unit

  let show _ = ""
end

module Parser = AMPCL.Parser.Char.String.Show.Make (Unit)
open Parser

(* function wise or - takes two functions that return boolean and ors when given an input *)
let ( |-> ) f g x = f x || g x
let ( & ) f g x = f (g x)

(* function wise and - takes two functions that return boolean and ands when given an input *)
let ( &-> ) f g x = f x && g x
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
