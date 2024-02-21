type ty =
  | Meta of int
  | TFunction of (ty * ty)
  | TUnit
  | TBool
  | TInteger
  | TFloat
  | TString
  | TPoly of int list * ty
  | TRowExtension of { label : string; field : ty; row_extension : ty }
    (* todo gadts so the row_extension can only be empty row or row extension *)
  | TEmptyRow
  | TRecord of
      ty (* todo gadts so this can only be empty row or row extension *)
  | TTuple of ty list (* todo variants are also rows *)
  | TVariant of (string * ty) list

let rec type_to_string ty type_delim delim empty =
  match ty with
  | TUnit -> "()"
  | TBool -> "bool"
  | TInteger -> "int"
  | TString -> "string"
  | TFloat -> "float"
  | Meta m -> "'" ^ string_of_int m
  | TFunction (t1, t2) ->
      "("
      ^ type_to_string t1 " " " " "{}"
      ^ ") -> ("
      ^ type_to_string t2 " " " " "{}"
      ^ ")"
  | TPoly (ms, t) ->
      "∀"
      ^ String.concat "," (List.map string_of_int ms)
      ^ "."
      ^ type_to_string t " " " " "{}"
  | TRecord fields ->
      "{ " ^ type_to_string fields ": " "; " "" ^ " }"
      (* to make printing work if we swithc variants/adts to rows is call type_to_string with delim = " | " and type_delim = " of " *)
  | TVariant fields ->
      String.concat " | "
        (List.map
                (fun (field, ty) -> field ^ " of " ^ type_to_string ty " " " " "{}")
           fields)
  | TTuple fields ->
      String.concat " * "
            (List.map (fun ty -> type_to_string ty " " " " "{}" ) fields)
  | TEmptyRow -> empty
  | TRowExtension { label; field; row_extension = TEmptyRow } ->
        label ^ type_delim ^ type_to_string field " " " " "{}"
  | TRowExtension { label; field; row_extension } ->
      label ^ type_delim
        ^ type_to_string field " " " " "{}"
      ^ delim
      ^ type_to_string row_extension type_delim delim ""

let type_to_string x = type_to_string x " " " " "{}"
