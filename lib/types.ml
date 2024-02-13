type ty =
  | Meta of int
  | TFunction of (ty * ty)
  | TUnit
  | TBool
  | TInteger
  | TFloat
  | TString
  | TPoly of int list * ty
  | TRecord of (string * ty) list
  | TTuple of ty list
  | TVariant of (string * ty) list

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
  | TRecord fields ->
      "{ "
      ^ String.concat "; "
          (List.map
             (fun (field, ty) -> field ^ ": " ^ type_to_string ty)
             fields)
      ^ " }"
  | TVariant fields ->
      String.concat " | "
        (List.map
           (fun (field, ty) -> field ^ " of " ^ type_to_string ty)
           fields)
  | TTuple fields ->
      String.concat " * " (List.map (fun ty -> type_to_string ty) fields)