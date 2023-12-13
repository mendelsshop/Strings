open AMPCL

let key_words = [ "if"; "then"; "else"; "fun" ]
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
    <|> (skip_garbage << word1 <$> fun ty -> Ast.Type ty)
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

let string_parser1 =
  many1 string_parser <$> fun ss ->
  Ast.String (implode (List.concat_map Fun.id ss))

let string_parser =
  many string_parser <$> fun ss ->
  Ast.String (implode (List.concat_map Fun.id ss))

let ident_parser =
  ( skip_garbage << seq letter (many (alphanum <|> char '_'))
  <$> fun (fst, snd) -> implode (fst :: snd) )
  >>= fun ident -> if not (List.mem ident key_words) then return ident else zero
(* todo: dont allow if then else let ... *)

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

let ident = ident_parser <|> infix_ident

let fun_params =
  many1
    ( seq ident (opt (skip_garbage << char ':' << type_parser))
    <$> fun (p, ty) -> { Ast.value = p; ty } )

let fun_parser expr =
  seq (string "fun" << fun_params >> (skip_garbage << string "->")) expr
  <$> fun (ps, exp) -> Ast.Function { parameters = ps; abstraction = exp }

let let_parser expr =
  string "let"
  << seq ident (seq (opt fun_params) (skip_garbage << (char '=' << expr)))
  <$> fun (name, (params, exp)) ->
  Ast.Let
    {
      name;
      value =
        (match params with
        | Some params -> Ast.Function { parameters = params; abstraction = exp }
        | None -> exp);
    }

let if_then_else expr =
  seq
    (skip_garbage << string "if" << expr)
    (seq
       (skip_garbage << string "then" << expr)
       (skip_garbage << string "else" << expr))
  <$> fun (condition, (consequent, alternative)) ->
  Ast.If { condition; consequent; alternative }

let number = many1 digit <$> fun ns -> Ast.Int (implode ns |> int_of_string)
let integer_opt = many digit
let integer = many1 digit
let decimal = char '.'

let float =
  let number_opt_dot_number = seq integer_opt (seq decimal integer)
  and number_dot_number_opt = seq integer (seq decimal integer_opt) in
  number_dot_number_opt <|> number_opt_dot_number
  <$> fun (f, ((_ : char), s)) ->
  Ast.Float (Float.of_string (implode (f @ ('.' :: s))))

let rec expr input =
  let constant =
    number <|> float <|> (char '\"' << string_parser >> char '\"')
  in
  let ident = ident <$> fun i -> Ast.Ident i in
  let parens =
    expr |> between (skip_garbage << char '(') (skip_garbage << char ')')
  in
  let atom = parens <|> (skip_garbage << (constant <|> ident)) in
  let basic_forms = if_then_else expr <|> fun_parser expr <|> atom in
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

let parser =
  many (string_parser1 <|> (char '\"' << expr >> (skip_garbage << char '\"')))
