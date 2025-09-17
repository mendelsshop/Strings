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
  letter <$> string_of_char
  >>= (fun first ->
  takeWhile is_hexadecimal <$> ( ^ ) first |> check (not_in keywords))
  |> tryP <?> "identifier"

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
  |> tryP <?> "infix identifier"

let identifier =
  basic_identifier |> tryP
  <|> (between (junk << char '(') (junk << char ')') infix_identifier
      <?> "infix identifier")

let infix_identifier = infix_identifier

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
  let field =
    seq identifier (junk << char assign << p) <$> fun (label, value) ->
    { label; value }
  in
  let field =
    match identifier_short_hand with
    | Some f ->
        field <|> (identifier <$> fun label -> { label; value = f label })
    | None -> field
  in
  between
    (junk << char '{')
    (junk << char '}')
    (seq (p >> string "with" |> opt) (sepby field (junk << char ';')))
  <?> "record"

(* variant parser is only used for types so it won't be ambiguous with application parser *)
let constructor p zero = seq variant_identifier (p <|> zero) <?> "constructor"

let rec typeP =
  let list_to_row ~k ~base list =
    (List.fold_right (fun { label; value } rest_row ->
         Union_find.make (TyRowExtend { label; field = value; rest_row })))
      list
      (Option.value ~default:(Union_find.make TyRowEmpty) base)
    |> k
  in

  Parser
    {
      unParse =
        (fun s ok err ->
          let basic_type =
            choice
              [
                unit <$> Fun.const (Union_find.make TyUnit);
                paren typeP;
                junk << string "integer"
                <$> Fun.const (Union_find.make TyInteger);
                junk << string "float" <$> Fun.const (Union_find.make TyFloat);
                junk << string "string" <$> Fun.const (Union_find.make TyString);
                junk << string "boolean"
                <$> Fun.const (Union_find.make TyBoolean);
                record typeP None ':'
                <$> (fun (base, row) ->
                list_to_row ~base
                  ~k:(fun row -> Union_find.make (TyRecord row))
                  row)
                <?> "record";
              ]
          in
          let variant =
            many1
              (seq variant_identifier
                 (opt basic_type
                 <$> Option.value ~default:(Union_find.make TyUnit)))
            <$> List.map (fun (label, value) -> { label; value })
            <$> list_to_row
                  ~k:(fun row -> Union_find.make (TyVariant row))
                  ~base:None
          in
          let functionP =
            variant <|> basic_type >>= fun domain ->
            opt (junk << string "->" << typeP)
            <$> Option.fold
                  ~some:(fun range ->
                    Union_find.make (TyArrow { domain; range }))
                  ~none:domain
          in

          let (Parser { unParse }) = functionP in
          unParse s ok err);
    }

let ascription p = seq p (junk << char ':' << typeP)

let type_signature =
  seq (string "type" << basic_identifier) (junk << char '=' << typeP)
  <$> fun (name, ty) -> TypeBind { name; ty }

let nominal_type_signature =
  seq (string "data" << basic_identifier) (junk << char '=' << typeP)
  <$> fun (name, ty) ->
  NominalTypeBind
    {
      name;
      ty = Union_find.make (TyNominal { name; ty; id = Utils.gensym_int () });
    }

let rec pattern =
  let record p identifier_short_hand assign =
    let field = seq identifier (junk << char assign << p) in
    let field =
      match identifier_short_hand with
      | Some f -> field <|> (identifier <$> fun field -> (field, f field))
      | None -> field
    in
    between
      (junk << char '{')
      (junk << char '}')
      (sepby field (junk << char ';'))
    <?> "record"
  in

  (* TODO: what is ascription's precedence *)
  Parser
    {
      unParse =
        (fun s ok err ->
          let (Parser { unParse }) =
            choice
              [
                paren pattern;
                ( junk << char '\"' << stringP >> char '\"' <$> fun s ->
                  PString s );
                (float <$> fun f -> Ast.PFloat f);
                ( constructor pattern (return PUnit) <$> fun (name, value) ->
                  PConstructor { name; value } );
                (number <$> fun i -> PInteger i);
                junk << char '_' <$> Fun.const PWildcard;
                (identifier <$> fun i -> PVar i);
                unit <$> Fun.const PUnit;
                ( record pattern (Some (fun i -> PVar i)) '='
                <$> List.map (fun (label, value) -> { label; value })
                <$> fun r -> PRecord r );
              ]
          in
          unParse s ok err);
    }

let unless b p = if b then return None else p <$> fun x -> Some x
let whenP b p = if b then p <$> fun x -> Some x else return None
let fun_params = many pattern
let fun_params1 = many1 pattern

let let_head is_rec expr =
  let expr = junk << char '=' << expr in
  let function_signature =
    return (fun name parameters e ->
        (PVar name, Lambda { parameters; body = e }))
    <*> identifier <*> fun_params1 <*> expr
  in
  let plain_let = seq pattern expr in
  junk << string "let"
  << whenP is_rec (junk << string "rec")
  << (function_signature <|> plain_let)

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
                       (*TODO: maybe only do this if in application*)
                       !->(String.starts_with ~prefix:"\n")
                       stringP
                  >> unless is_end (char '\"' <?> "end of expression")
                  <$> fun s -> String s );
                  float <$> (fun f -> Ast.Float f) >> last_quote is_end;
                  (* TODO: for construction should a "constructor" be no different than an application, meaning that each constructor is a n-ary function, that can be destructed into its values, would also have to update type parsing to handle this *)
                  constructor (basic_expr is_end)
                    (last_quote is_end <$> Fun.const Unit)
                  <$> (fun (name, value) -> Constructor { name; value })
                  >> last_quote is_end;
                  number <$> (fun i -> Integer i) >> last_quote is_end;
                  identifier <$> (fun i -> Var i) >> last_quote is_end;
                  unit <$> Fun.const Unit >> last_quote is_end;
                  record (expr false) (Some (fun i -> Var i)) '='
                  <$> (fun (record, new_fields) ->
                  Option.fold
                    ~some:(fun record -> RecordExtend { record; new_fields })
                    ~none:(Ast.Record new_fields) record)
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
      << ( identifier <$> fun projector record ->
           RecordAccess { record; projector } ))
    <$> List.fold_left ( |> ) value
    >> last_quote is_end)
    <|> basic_expr is_end
  in
  let application is_end =
    if is_end then
      let rec go func =
        let get_func func arguement =
          Option.fold ~none:arguement
            ~some:(fun lambda -> Application { lambda; arguement })
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
            (fun lambda arguement -> Application { lambda; arguement })
            single list
      | [] -> failwith "unreachable"
  in

  (* TODO: infix *)
  let rec ifP is_end =
    let expr is_end = ifP is_end <|> application is_end in
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
              If { condition; consequent; alternative }
            in
            unParse s ok err);
      }
  in
  let funP expr =
    seq (junk << string "fun" << fun_params >> (junk << string "->")) expr
    <$> fun (parameters, body) -> Lambda { parameters; body }
  in
  let letP expr is_end =
    let endP = junk << string "in" << expr is_end in
    return (fun (name, e1) e2 -> LetRec { name; e1; e2 })
    <*> let_head true (expr false)
    <*> endP
    <|> (return (fun (name, e1) e2 -> Let { name; e1; e2 })
        <*> let_head false (expr false)
        <*> endP)
  in

  let case expr is_end =
    let case is_end =
      (* TODO: multi or pattern *)
      seq (junk << pattern) (junk << string "->" << expr is_end)
      <$> fun (pattern, result) -> { pattern; result }
    in
    junk << string "match" << junk << expr false >> junk >> string "with"
    >>= fun value ->
    (if is_end then
       let end_cases =
         makeRecParser (fun parser ->
             choice
               [
                 return List.cons
                 <*> (junk << char '|' << case false)
                 <*> parser;
                 (junk << char '|' << case true <$> fun end_case -> [ end_case ]);
               ])
       in
       seq (junk << char '|' |> opt << case false) end_cases
       <$> (fun (c, cases) -> c :: cases)
       <|> (junk << char '|' |> opt << case is_end <$> fun case -> [ case ])
     else
       seq
         (junk << char '|' |> opt << case false)
         (junk << char '|' << case false |> many)
       <$> fun (c, cs) -> c :: cs)
    <$> fun cases -> Match { value; cases }
  in
  let expr' is_end = ifP is_end <|> application is_end in

  let rec expr is_end =
    Parser
      {
        unParse =
          (fun s ok err ->
            let (Parser { unParse }) =
              choice
                [
                  expr' is_end;
                  case expr is_end <?> "match";
                  funP (expr is_end);
                  letP expr is_end;
                ]
            in
            unParse s ok err);
      }
  in
  expr is_end

let letP =
  let_head true (expr true)
  <$> (fun (name, value) -> RecBind { name; value })
  <|> (let_head false (expr true) <$> fun (name, value) -> Bind { name; value })

let top_level =
  char '\"'
  << choice (* TODO: maybe allow mutliple top level term in single quotes *)
       [
         letP;
         (expr true <$> fun expr -> Bind { name = PWildcard; value = expr });
         (* TODO: maybe consume new line *)
         type_signature >> junk >> char '\"';
         nominal_type_signature >> junk >> char '\"';
       ]
  <|> (stringP1 <?> "top level string" <$> fun string -> Ast.PrintString string)

let parse = many1 top_level >> eof
let run = run_show
