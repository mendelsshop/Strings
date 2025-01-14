open Types
open Ast

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

let reserved_operators = [ "->"; "."; "_" ]
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
    (takeWhile (( <> ) '\n' &-> ( <> ) '\"'))
  <?> "comment"

let multi_line_comment =
  between (char '#') (char '#') (takeWhile (( <> ) '#')) <?> "comment"

let takeWhile1 p =
  sat p <$> string_of_char >>= fun first -> takeWhile p <$> ( ^ ) first

let white_space = takeWhile1 is_white_space
let comment = line_comment <|> multi_line_comment
let junk = many (comment <|> white_space)

let basic_identifier_without_junk =
  letter <$> string_of_char >>= fun first ->
  takeWhile is_hexadecimal <$> ( ^ ) first
  |> check (not_in keywords)
  <?> "identifier"

let basic_identifier = junk << basic_identifier_without_junk

let infix_identifier =
  (* comment symbols are allowed in infix identifiers *)
  let not_infix_symbols =
    is_hexadecimal |-> is_white_space
    |-> (Fun.flip List.mem) [ '('; ')'; '['; ']'; '\"'; '{'; '}' ]
  in
  let infix_symbols = !->not_infix_symbols in
  junk << sat (infix_symbols &-> ( <> ) '`') <$> string_of_char >>= fun start ->
  takeWhile infix_symbols <$> ( ^ ) start
  |> check (not_in reserved_operators)
  <?> "infix identifier"

let identifier =
  basic_identifier
  <|> (between (junk << char '(') (junk << char ')') infix_identifier
      <?> "infix identifier")

(* TODO: for infix too *)
let variant_identifier = junk << char '`' << identifier
let number_inner = takeWhile is_decimal
let number1_inner = takeWhile1 is_decimal
let number = junk << number1_inner <$> int_of_string <?> "number"

let float =
  junk
  << (number1_inner
     >>= (fun first -> char '.' << number_inner <$> ( ^ ) (first ^ "."))
     <|> ( number_inner >>= fun first ->
           char '.' << number1_inner <$> ( ^ ) (first ^ ".") ))
  <$> float_of_string <?> "float"

let escaped =
  let parse_to_char format =
    char_of_int & int_of_string & ( ^ ) format & AMPCL.implode
  in
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
  let octal = count 3 (sat is_octal) <$> parse_to_char "0o" in
  let hex2 = char 'x' << count 2 alphanum <$> parse_to_char "0x" in
  let hex4 = char 'u' << count 4 alphanum <$> parse_to_char "0x" in
  let hex8 = char 'U' << count 8 alphanum <$> parse_to_char "0x" in
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

let stringP_inner = escaped <|> sat (( <> ) '\"')
let stringP = many stringP_inner <$> AMPCL.implode <?> "string"
let stringP1 = many1 stringP_inner <$> AMPCL.implode <?> "string"

let unit : unit t =
  junk << char '(' << junk << char ')' <$> Fun.const () <?> "unit"

let paren p = between (junk << char '(') (junk << char ')') p <?> "paren"

let record p identifier_short_hand assign =
  let field = seq identifier (junk << char assign << p) in
  let field =
    match identifier_short_hand with
    | Some f -> field <|> (identifier <$> fun field -> (field, f field))
    | None -> field
  in
  between (junk << char '{') (junk << char '}') (sepby field (junk << char ';'))
  <?> "record"

(* variant parser is only used for types so it won't be ambiguous with application parser *)
let constructor p zero = seq variant_identifier (p <|> zero) <?> "constructor"

let rec typeP =
  let list_to_row =
    Fun.flip
      (List.fold_right (fun (name, ty) row ->
           TRowExtension { label = name; field = ty; row_extension = row }))
      TEmptyRow
  in

  Parser
    {
      unParse =
        (fun s ok err ->
          let basic_type =
            choice
              [
                unit <$> Fun.const TUnit;
                paren typeP;
                junk << string "int" <$> Fun.const TInteger;
                junk << string "float" <$> Fun.const TFloat;
                junk << string "string" <$> Fun.const TString;
                junk << string "bool" <$> Fun.const TBool;
                record typeP None ':'
                <$> ((fun row -> TRecord row) & list_to_row)
                <?> "record";
              ]
          in
          let tuple =
            sepby1 basic_type (junk << char '*') <$> function
            | t :: [] -> t
            | t -> TTuple t
          in
          let variant =
            many1
              (seq variant_identifier
                 (opt basic_type <$> Option.value ~default:TUnit))
            <$> ((fun row -> TVariant row) & list_to_row)
          in
          let functionP =
            variant <|> tuple >>= fun first ->
            opt (junk << string "->" << typeP)
            <$> Option.fold
                  ~some:(fun return -> TFunction (first, return))
                  ~none:first
          in

          let (Parser { unParse }) = functionP in
          unParse s ok err);
    }

let ascription p = seq p (junk << char ':' << typeP)

let rec pattern =
  (* TODO: what is ascription's precedence *)
  Parser
    {
      unParse =
        (fun s ok err ->
          let (Parser { unParse }) =
            let basic_pattern =
              choice
                [
                  paren pattern;
                  ( junk << char '\"' << stringP >> char '\"' <$> fun s ->
                    PString s );
                  (float <$> fun f -> Ast.PFloat f);
                  ( constructor pattern (return PUnit) <$> fun (name, value) ->
                    PConstructor { name; value } );
                  (number <$> fun i -> Ast.PInt i);
                  junk << char '_' <$> Fun.const PWildCard;
                  (identifier <$> fun i -> Ast.PIdent i);
                  unit <$> Fun.const PUnit;
                  ( record pattern (Some (fun i -> PIdent i)) '='
                  <$> List.map (fun (name, value) -> { name; value })
                  <$> fun r -> PRecord r );
                ]
            in

            sepby1 basic_pattern (junk << char ',') <$> function
            | t :: [] -> t
            | t -> PTuple t
          in

          unParse s ok err);
    }

let unless b p = if b then return None else p <$> fun x -> Some x
let fun_params = many pattern
let fun_params1 = many1 pattern

let rec expr is_end =
  let last_quote is_end =
    unless (not is_end) (junk << char '\"' << char '\n' <?> "end of expression")
  in
  let rec basic_expr is_end =
    Parser
      {
        unParse =
          (fun s ok err ->
            let (Parser { unParse }) =
              choice
                [
                  paren (expr false) >> last_quote is_end;
                  ( junk << char '\"' <?> "start of string"
                  << check
                       (* make sure that last expression is not string starting with newline *)
                       (Fun.const (not is_end)
                       |-> !->(String.starts_with ~prefix:"\n"))
                       stringP
                  >> unless is_end (char '\"' <?> "end of expression")
                  <$> fun s -> String s );
                  float <$> (fun f -> Ast.Float f) >> last_quote is_end;
                  (* TODO: for construction should a "constructor" be no different than an application, meaning that each constructor is a n-ary function, that can be destructed into its values, would also have to update type parsing to handle this *)
                  constructor (basic_expr is_end)
                    (last_quote is_end <$> Fun.const Unit)
                  <$> (fun (name, value) -> Constructor { name; value })
                  >> last_quote is_end;
                  number <$> (fun i -> Ast.Int i) >> last_quote is_end;
                  identifier <$> (fun i -> Ast.Ident i) >> last_quote is_end;
                  unit <$> Fun.const Unit >> last_quote is_end;
                  record (expr false) (Some (fun i -> Ident i)) '='
                  <$> List.map (fun (name, value) -> { name; value })
                  <$> (fun r -> Record r)
                  >> last_quote is_end;
                ]
            in
            unParse s ok err);
      }
  in

  let project is_end () =
    basic_expr false
    >>= (fun value ->
    many
      (junk << char '.'
      << (identifier
         <$> (fun projector value -> RecordAcces { value; projector })
         <|> (number <$> fun projector value -> TupleAcces { value; projector })
         ))
    <$> List.fold_left ( |> ) value
    >> last_quote is_end)
    <|> basic_expr is_end
  in
  let application is_end =
    if is_end then
      let rec go func =
        let get_func func arguement =
          Option.fold ~none:arguement
            ~some:(fun func -> Application { func; arguement })
            func
        in
        project false ()
        >>= (go & Option.some & get_func func)
        <|> (project true () <$> get_func func)
      in
      go None
    else
      many1 (project false ()) <$> function
      | single :: list ->
          List.fold_left
            (fun app current -> Application { func = app; arguement = current })
            single list
      | [] -> failwith "unreachable"
  in

  (* TODO: infix *)
  let tuple is_end =
    (if is_end then
       let rec go =
         Parser
           {
             unParse =
               (fun s ok err ->
                 let (Parser { unParse }) =
                   return List.cons <*> application false >> char ',' <*> go
                   <|> (application true <$> Fun.flip List.cons [])
                 in
                 unParse s ok err);
           }
       in
       go
     else sepby1 (application false) (junk << char ','))
    <$> function
    | x :: [] -> x
    | xs -> Tuple xs
  in

  let rec ifP is_end =
    let expr is_end = ifP is_end <|> tuple is_end in
    Parser
      {
        unParse =
          (fun s ok err ->
            let (Parser { unParse }) =
              seq
                (junk << string "if" << expr false)
                (seq
                   (junk << string "then" << expr false)
                   (junk << string "else" << expr is_end))
              <$> fun (condition, (consequent, alternative)) ->
              Ast.If { condition; consequent; alternative }
            in
            unParse s ok err);
      }
  in
  let funP expr =
    seq (junk << string "fun" << fun_params >> (junk << string "->")) expr
    <$> fun (ps, exp) -> Ast.Function { parameters = ps; abstraction = exp }
  in
  let letP expr is_end =
    let rec_parser =
      junk << string "rec" << seq identifier fun_params1
      <$> (fun (name, params) (e1, e2) ->
      LetRec
        { name; e1 = Function { parameters = params; abstraction = e1 }; e2 })
      <|> ( seq pattern fun_params <$> fun (name, params) (e1, e2) ->
            Let
              {
                name;
                e1 =
                  (if List.is_empty params then e1
                   else Function { parameters = params; abstraction = e1 });
                e2;
              } )
      >>= fun cons ->
      junk
      << seq (char '=' << expr false) (junk << string "in" << expr is_end)
      <$> cons
    in
    junk << string "let" << junk << rec_parser
  in
  let case expr is_end =
    let case is_end =
      (* TODO: multi or pattern *)
      seq (junk << pattern) (junk << string "->" << expr is_end)
      <$> fun (pattern, result) -> { pattern; result }
    in
    junk << string "match" << junk << expr false >> junk >> string "with"
    >>= fun expr ->
    (if is_end then
       seq
         (junk << char '|' |> opt << case false)
         (seq
            (junk << char '|' << case false |> many)
            (junk << char '|' |> opt << case is_end))
       <$> (fun (c, (cs, last)) -> (c :: cs) @ [ last ])
       <|> (junk << char '|' |> opt << case is_end <$> fun case -> [ case ])
     else
       seq
         (junk << char '|' |> opt << case false)
         (junk << char '|' << case false |> many)
       <$> fun (c, cs) -> c :: cs)
    <$> fun cases -> Ast.Match { cases; expr }
  in
  let expr' is_end = ifP is_end <|> tuple is_end in

  let rec expr is_end =
    Parser
      {
        unParse =
          (fun s ok err ->
            let (Parser { unParse }) =
              expr' is_end
              <|> funP (expr is_end)
              <|> case expr is_end <|> letP expr is_end
            in
            unParse s ok err);
      }
  in
  expr is_end

let letP =
  let rec_parser =
    junk << string "rec" << seq identifier fun_params1
    <$> (fun (name, params) e ->
    RecBind { name; value = Function { parameters = params; abstraction = e } })
    <|> ( seq pattern fun_params <$> fun (name, params) e ->
          Bind
            {
              name;
              value =
                (if List.is_empty params then e
                 else Function { parameters = params; abstraction = e });
            } )
    >>= fun cons -> junk << (char '=' << expr true) <$> cons
  in
  junk << string "let" << junk << rec_parser

let top_level =
  char '\"'
  << (letP
     <|> (expr true <$> fun expr -> Ast.Bind { name = PWildCard; value = expr })
     )
  <|> (stringP1 <?> "top level string" <$> fun string -> Ast.PrintString string)

let parser = many1 top_level >> eof
let run = run_show
