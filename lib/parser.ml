open AMPCL
open Ast
open Types

let key_words = [ "type"; "in"; "let"; "if"; "then"; "else"; "fun" ]
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
    skip_garbage << char '(' << skip_garbage << char ')'
    <$> (fun _ -> TUnit)
    <|> between
          (skip_garbage << char '(')
          (skip_garbage << char ')')
          type_parser
    <|> (skip_garbage << string "int" <$> fun _ -> TInteger)
    <|> (skip_garbage << string "unit" <$> fun _ -> TUnit)
    <|> (skip_garbage << string "float" <$> fun _ -> TFloat)
    <|> (skip_garbage << string "bool" <$> fun _ -> TBool)
    <|> (skip_garbage << string "string" <$> fun _ -> TString)
  in
  let tuple_type =
    skip_garbage << char '*' << basic_type |> many1 |> opt |> seq basic_type
    <$> function
    | ty, None -> ty
    | ty, Some tys -> TTuple (ty :: tys)
  in
  let opt_fn = opt (skip_garbage << string "->" << type_parser) in
  let full_parser = seq tuple_type opt_fn in
  ( full_parser <$> fun (t1, (opt_t2 : ty option)) ->
    Option.fold ~none:t1 ~some:(fun t2 -> TFunction (t1, t2)) opt_t2 )
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

let string_parser1 =
  many1 string_parser <$> fun ss ->
  Ast.PrintString (implode (List.concat_map Fun.id ss))

let string_parser =
  many string_parser <$> fun ss -> implode (List.concat_map Fun.id ss)

let ident_parser =
  check
    (fun x -> not (List.mem x key_words))
    ( skip_garbage << seq lower (many (alphanum <|> char '_'))
    <$> fun (fst, snd) -> implode (fst :: snd) )

let inspect chars =
  implode chars |> print_endline;
  Some ((), chars)

let record_type_parser =
  let record = seq ident_parser (skip_garbage << char ':' << type_parser) in
  let record_mid = record >> (skip_garbage << char ';') in
  skip_garbage << char '{'
  << (many1 record_mid
     >> (skip_garbage << char '}')
     <|> (seq (many record_mid) record
         <$> (fun (rs, r) -> rs @ [ r ])
         >> (skip_garbage >> char '}')))
  <$> fun rs ->
  TRecord
    (List.fold_left
       (fun row field ->
         TRowExtension
           { label = fst field; field = snd field; row_extension = row })
       TEmptyRow rs)

let variant_ident_parser =
  skip_garbage << seq upper (alphanum |> many) <$> fun (c, cs) ->
  implode (c :: cs)

let variant_type_parser =
  let variant =
    seq variant_ident_parser
      (skip_garbage << string "of" << (record_type_parser <|> type_parser))
  in
  let variant_with_sep f = skip_garbage << char '|' |> f << variant in
  seq (variant_with_sep opt) (variant_with_sep Fun.id |> many)
  <$> fun (v, vs) -> TVariant (v :: vs)

let type_def_parser =
  seq
    (string "type" << skip_garbage << ident_parser)
    (skip_garbage << char '='
    << (variant_type_parser <|> record_type_parser <|> type_parser))
  <$> fun (name, ty) -> Ast.TypeBind { name; ty }

let start_infix_symbols =
  [ '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|' ]

let infix_symbols = [ '!'; '?'; '~' ] @ start_infix_symbols

let infix =
  (fun c -> List.mem c start_infix_symbols)
  |> sat |> many
  |> seq (skip_garbage << sat (fun c -> List.mem c start_infix_symbols))
  <$> fun (fst, rst) -> implode (fst :: rst)

let infix_ident =
  infix |> between (skip_garbage << char '(') (skip_garbage << char ')')

let ident =
  ident_parser <|> infix_ident
  (* TODO: make unit expression instead of "()"*)
  <|> (skip_garbage << char '(' << skip_garbage << char ')' <$> fun _ -> "()")

let fun_params =
  many1
    (ident
    <$> (fun i -> { ident = i; ty = None })
    <|> ( seq
            (skip_garbage << char '(' << ident)
            (skip_garbage << char ':' << skip_garbage << type_parser
            >> (skip_garbage << char ')'))
        <$> fun (i, ty) -> { ident = i; ty = Some ty } ))

let fun_parser expr =
  seq
    (skip_garbage << string "fun" << fun_params >> (skip_garbage << string "->"))
    expr
  <$> fun (ps, exp) -> Ast.Function { parameters = ps; abstraction = exp }

let let_parser expr =
  skip_garbage << string "let" << skip_garbage
  << seq
       (opt (string "rec"))
       (seq ident (seq (opt fun_params) (skip_garbage << (char '=' << expr))))
  <$> fun (is_rec, (name, (params, exp))) ->
  if Option.is_some is_rec then
    RecBind
      {
        name;
        value =
          (match params with
          | Some params ->
              Ast.Function { parameters = params; abstraction = exp }
          | None -> exp);
      }
  else
    Bind
      {
        name;
        value =
          (match params with
          | Some params ->
              Ast.Function { parameters = params; abstraction = exp }
          | None -> exp);
      }

let let_expr_parser expr =
  skip_garbage << string "let" << skip_garbage
  << seq
       (opt (string "rec"))
       (seq ident
          (seq (opt fun_params)
             (skip_garbage
             << (char '=' << seq expr (skip_garbage << string "in" << expr)))))
  <$> fun (is_rec, (name, (params, (e1, e2)))) ->
  if Option.is_some is_rec then
    LetRec
      {
        name;
        e1 =
          (match params with
          | Some params ->
              Ast.Function { parameters = params; abstraction = e1 }
          | None -> e1);
        e2;
      }
  else
    Let
      {
        name;
        e1 =
          (match params with
          | Some params ->
              Ast.Function { parameters = params; abstraction = e1 }
          | None -> e1);
        e2;
      }

let if_then_else expr =
  seq
    (skip_garbage << string "if" << expr)
    (seq
       (skip_garbage << string "then" << expr)
       (skip_garbage << string "else" << expr))
  <$> fun (condition, (consequent, alternative)) ->
  Ast.If { condition; consequent; alternative }

let number wrapper =
  many1 digit <$> fun ns -> implode ns |> int_of_string |> wrapper

let integer_opt = many digit
let integer = many1 digit
let decimal = char '.'

let float wrapper =
  let number_opt_dot_number = seq integer_opt (seq decimal integer)
  and number_dot_number_opt = seq integer (seq decimal integer_opt) in
  number_dot_number_opt <|> number_opt_dot_number
  <$> fun (f, ((_ : char), s)) ->
  Float.of_string (implode (f @ ('.' :: s))) |> wrapper

let record wrapper ident expr =
  let record =
    seq ident_parser (opt (skip_garbage << char '=' << expr)) <$> function
    | name, None -> { name; value = ident name }
    | name, Some value -> { name; value }
  in
  let record_mid = record >> (skip_garbage << char ';') in
  skip_garbage << char '{'
  << (many1 record_mid
     >> (skip_garbage << char '}')
     <|> (seq (many record_mid) record
         <$> (fun (rs, r) -> rs @ [ r ])
         >> (skip_garbage >> char '}')))
  <$> wrapper

let tuple wrapper expr =
  skip_garbage << char ',' << expr |> many |> seq expr <$> function
  | x, [] -> x
  | x, xs -> x :: xs |> wrapper

let variant wrapper expr =
  seq variant_ident_parser expr <$> fun (name, value) -> wrapper name value

let parens expr =
  expr |> between (skip_garbage << char '(') (skip_garbage << char ')')

let rec pattern_parser input =
  input
  |> (parens pattern_parser
     <|> float (fun f -> Ast.PFloat f)
     <|> number (fun i -> Ast.PInt i)
     <|> (ident <$> fun i -> if i = "_" then PWildCard else Ast.PIdent i)
     <|> ( skip_garbage << char '(' << skip_garbage << char ')' <$> fun _ ->
           Ast.PUnit )
     <|> record (fun r -> PRecord r) (fun i -> PIdent i) pattern_parser
     |> tuple (fun t -> PTuple t))

let rec expr input =
  let constant =
    float (fun f -> Ast.Float f)
    <|> number (fun i -> Ast.Int i)
    (* if a quote within a quoted expression is found before a new line it means the quoted expression is done otherwise whattever follows untill next quote is to be part of the quoted expression *)
    <|> (char '\"'
        << sat (fun c -> c <> '\n')
        >>= (fun c ->
              string_parser <$> fun str -> Ast.String (string_of_char c ^ str))
        >> char '\"')
  in
  (* TODO: differtiate between tuple and record projection *)
  let project expr =
    skip_garbage << char '.'
    << (ident_parser <|> infix_ident
       <|> (skip_garbage << many1 digit <$> implode))
    |> opt |> seq expr
    <$> function
    | value, Some projector ->
        Option.fold
          ~none:(RecordAcces { value; projector })
          ~some:(fun projector -> TupleAcces { value; projector })
          (int_of_string_opt projector)
    | value, None -> value
  in
  let ident = ident <$> fun i -> Ast.Ident i in
  let atom = parens expr <|> (skip_garbage << constant) <|> ident in
  let basic_forms =
    let_expr_parser expr <|> if_then_else expr <|> fun_parser expr
    <|> variant (fun name value -> Constructor { name; value }) expr
    <|> record (fun r -> Record r) (fun i -> Ident i) expr
    <|> atom
  in
  let basic_forms = tuple (fun t -> Tuple t) (project basic_forms) in
  let application =
    let rec application_tail func input =
      ( basic_forms >>= fun arguement ->
        let new_func = Ast.Application { func; arguement } in
        application_tail new_func <|> return new_func )
        input
    in
    basic_forms >>= fun func -> application_tail func <|> return func
  in
  let rec infix_application input =
    ( seq application (opt (seq infix infix_application)) <$> fun (e1, infix) ->
      match infix with
      | Some (infix, e2) ->
          Ast.InfixApplication { infix; arguements = (e1, e2) }
      | None -> e1 )
      input
  in
  infix_application input

let top_level = expr <$> fun exp -> Ast.Bind { name = "()"; value = exp }

let parser =
  many
    (string_parser1
    <$> (fun x -> x :: [])
    <|> (char '\"'
        (* top level has to be attempted before top level let b/c let will parse let .. in as let with the remaining in left unparsed *)
        << many (top_level <|> let_parser expr <|> type_def_parser)
        >> (skip_garbage << char '\"')))
  <$> List.concat

let run = run
