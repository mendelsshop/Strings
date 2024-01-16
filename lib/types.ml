type ty =
  | Meta of int
  | TFunction of (ty * ty)
  | TUnit
  | TBool
  | TInteger
  | TFloat
  | TString
  | TPoly of int list * ty


let rec type_to_string ty =
  match ty with
  | TUnit -> "()"
  | TBool -> "bool"
  | TInteger -> "int"
  | TString -> "string"
  | TFloat -> "float"
  | Meta m -> "'" ^ string_of_int m
  | TFunction (t1, t2) ->
      "(" ^ type_to_string t1 ^ ") -> (" ^ type_to_string t2 ^ ")"
  | TPoly (ms, t) ->
      "∀"
      ^ String.concat "," (List.map string_of_int ms)
      ^ "." ^ type_to_string t
