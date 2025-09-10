(* <<<<<<< HEAD *)
open Types
open Ast

(* ======= *)
open AMPCL
(* >>>>>>> ml/main *)

module Unit = struct
  include Unit

  let show _ = ""
end

module Parser = AMPCL.Parser.Char.String.Show.Make (Unit)
open Parser

(* <<<<<<< HEAD *)
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
  between
    (junk << char '{')
    (junk << char '}')
    (seq (p >> string "with" |> opt) (sepby field (junk << char ';')))
  <?> "record"

(* variant parser is only used for types so it won't be ambiguous with application parser *)
let constructor p zero = seq variant_identifier (p <|> zero) <?> "constructor"

let rec typeP =
  let list_to_row ~k ~base list =
    (List.fold_right (fun (name, ty) row ->
         Union_find.make (TyRowExtend (name, ty, row))))
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
                junk << string "int" <$> Fun.const (Union_find.make TyInteger);
                junk << string "float" <$> Fun.const (Union_find.make TyFloat);
                junk << string "string" <$> Fun.const (Union_find.make TyString);
                junk << string "bool" <$> Fun.const (Union_find.make TyBoolean);
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
            <$> list_to_row
                  ~k:(fun row -> Union_find.make (TyVariant row))
                  ~base:None
          in
          let functionP =
            variant <|> basic_type >>= fun first ->
            opt (junk << string "->" << typeP)
            <$> Option.fold
                  ~some:(fun return ->
                    Union_find.make (TyArrow (first, return)))
                  ~none:first
          in

          let (Parser { unParse }) = functionP in
          unParse s ok err);
    }

let ascription p = seq p (junk << char ':' << typeP)

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
                  PConstructor (name, value) );
                (number <$> fun i -> PInteger i);
                junk << char '_' <$> Fun.const PWildcard;
                (identifier <$> fun i -> PVar i);
                unit <$> Fun.const PUnit;
                ( record pattern (Some (fun i -> PVar i)) '='
                <$> List.map (fun (name, value) -> (name, value))
                <$> fun r -> PRecord r );
              ]
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
                       (*TODO: maybe only do this if in application*)
                       !->(String.starts_with ~prefix:"\n")
                       stringP
                  >> unless is_end (char '\"' <?> "end of expression")
                  <$> fun s -> String s );
                  float <$> (fun f -> Ast.Float f) >> last_quote is_end;
                  (* TODO: for construction should a "constructor" be no different than an application, meaning that each constructor is a n-ary function, that can be destructed into its values, would also have to update type parsing to handle this *)
                  constructor (basic_expr is_end)
                    (last_quote is_end <$> Fun.const Unit)
                  <$> (fun (name, value) -> Constructor (name, value))
                  >> last_quote is_end;
                  number <$> (fun i -> Integer i) >> last_quote is_end;
                  identifier <$> (fun i -> Var i) >> last_quote is_end;
                  unit <$> Fun.const Unit >> last_quote is_end;
                  record (expr false) (Some (fun i -> Var i)) '='
                  <$> (fun (base, rows) ->
                  (fun rows ->
                    Option.fold
                      ~some:(fun base -> RecordExtend (base, rows))
                      ~none:(Ast.Record rows) base)
                    (List.map (fun (name, value) -> (name, value)) rows))
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
      << (identifier <$> fun projector value -> RecordAccess (value, projector))
      )
    <$> List.fold_left ( |> ) value
    >> last_quote is_end)
    <|> basic_expr is_end
  in
  let application is_end =
    if is_end then
      let rec go func =
        let get_func func arguement =
          Option.fold ~none:arguement
            ~some:(fun func -> Application (func, arguement))
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
            (fun app current -> Application (app, current))
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
              If (condition, consequent, alternative)
            in
            unParse s ok err);
      }
  in
  let funP expr =
    seq (junk << string "fun" << fun_params >> (junk << string "->")) expr
    <$> fun (ps, exp) -> Lambda (ps, exp)
  in
  let letP expr is_end =
    let rec_parser =
      junk << string "rec" << seq pattern fun_params1
      <$> (fun (name, params) (e1, e2) ->
      LetRec (name, Lambda (params, e1), e2))
      <|> ( seq pattern fun_params <$> fun (name, params) (e1, e2) ->
            Let
              ( name,
                (if List.is_empty params then e1 else Lambda (params, e1)),
                e2 ) )
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
      <$> fun (pattern, result) -> (pattern, result)
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
    <$> fun cases -> Match (expr, cases)
  in
  let expr' is_end = ifP is_end <|> application is_end in

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
    junk << string "rec" << seq pattern fun_params1
    <$> (fun (name, params) e -> RecBind { name; value = Lambda (params, e) })
    <|> ( seq pattern fun_params <$> fun (name, params) e ->
          Bind
            {
              name;
              value = (if List.is_empty params then e else Lambda (params, e));
            } )
    >>= fun cons -> junk << (char '=' << expr true) <$> cons
  in
  junk << string "let" << junk << rec_parser

let top_level =
  char '\"'
  << (letP
     <|> (expr true <$> fun expr -> Bind { name = PWildcard; value = expr }))
  <|> (stringP1 <?> "top level string" <$> fun string -> Ast.PrintString string)

let parser = many1 top_level >> eof

(* ======= *)
let key_words =
  [ "match"; "with"; "in"; "let"; "if"; "rec"; "then"; "else"; "\\"; "."; "|" ]

let junk =
  let non_newline = sat (fun c -> c != '\n') in
  let comment_contents = many non_newline <$> implode in
  let comment =
    string "--" >>= fun comment_start ->
    comment_contents <$> fun contents -> comment_start ^ contents
  in
  let white_space = sat (function ' ' | '\n' | '\t' -> true | _ -> false) in
  let white_spaces = white_space <$> String.make 1 in
  many (white_spaces <|> comment) <$> String.concat ""

let skip_garbage f = junk >>= fun _ -> f
let ( << ) f g x = f (g x)
let ( ! ) = skip_garbage

(*TODO: comments and whitespace*)

let number_parser wrapper =
  many1 digit <$> (float_of_int << int_of_string << implode) <$> wrapper

let boolean_parser wrapper =
  let true_parser = string "true" <$> fun _ -> wrapper true in
  let false_parser = string "false" <$> fun _ -> wrapper false in
  true_parser <|> false_parser

let ident =
  let idents = many alphanum in
  let flatten (f, rest) = f :: rest in
  seq lower idents <$> flatten <$> implode
  |> check (fun x -> not (List.mem x key_words))

let variant_ident =
  let idents = many alphanum in
  let flatten (f, rest) = f :: rest in
  keep_right (char '`')
    (seq letter idents <$> flatten <$> implode
    |> check (fun x -> not (List.mem x key_words)))

let ident_parser wrapper = ident <$> wrapper

let parens_parser expr =
  char '(' >>= fun _ ->
  expr >>= fun expr ->
  !(char ')') <$> fun _ -> expr

(*|> many*)
(*List.fold*)
(*<$> ( List.fold_left wrapper e1)*)
(*function*)
(*| [] -> e1*)
(*| tuples -> wrapper (e1, e2)*)
let record expr =
  (let ( << ) = keep_right in
   let record =
     seq !ident (opt (!(char '=') << expr)) <$> function
     | name, None -> (name, PVar name)
     | name, Some value -> (name, value)
   in
   let record_mid = record >> !(char ';') in
   !(char '{')
   << (many record_mid
      >> !(char '}')
      <|> (seq (many record_mid) record
          <$> (fun (rs, r) -> rs @ [ r ])
          >> !(char '}'))))
  <$> fun r -> PRecord r

let variant_parser wrapper expr =
  seq variant_ident expr <$> fun (name, expr) -> wrapper name expr

let pattern =
  makeRecParser (fun pattern ->
      !(choice
          [
            parens_parser pattern;
            (char '_' <$> fun _ -> PWildcard);
            ident_parser (fun i -> PVar i);
            (* number_parser (fun n -> PNumber n); *)
            boolean_parser (fun b -> PBoolean b);
            record pattern;
            variant_parser (fun name p -> PConstructor (name, p)) pattern;
          ]))

let lambda_parser expr =
  char '\\' >>= fun _ ->
  !pattern >>= fun ident ->
  !(char '.') >>= fun _ ->
  expr <$> fun expr -> Lambda ([ ident ], expr)

let if_parser expr =
  string "if" >>= fun _ ->
  expr >>= fun cond ->
  !(string "then") >>= fun _ ->
  expr >>= fun cons ->
  !(string "else") >>= fun _ ->
  expr <$> fun alt -> If (cond, cons, alt)

let record expr =
  (let ( << ) = keep_right in
   let record =
     seq !ident (opt (!(char '=') << expr)) <$> function
     | name, None -> (name, Var name)
     | name, Some value -> (name, value)
   in
   let record_mid = record >> !(char ';') in
   !(char '{')
   << seq
        (expr >> !(string "with") |> opt)
        (many1 record_mid
        >> !(char '}')
        <|> (seq (many record_mid) record
            <$> (fun (rs, r) -> rs @ [ r ])
            >> !(char '}'))))
  <$> function
  | Some init, rows -> RecordExtend (init, rows)
  | None, rows -> Record rows

let let_parser expr =
  string "let" >>= fun _ ->
  opt !(string "rec") >>= fun _rec ->
  !pattern >>= fun ident ->
  !(char '=') >>= fun _ ->
  expr >>= fun e1 ->
  !(string "in") >>= fun _ ->
  expr <$> fun e2 ->
  if Option.is_some _rec then LetRec (ident, e1, e2) else Let (ident, e1, e2)

let record_acces_parser expr =
  expr >>= fun record ->
  many (char '.' >>= fun _ -> ident) <$> fun acceses ->
  List.fold_left
    (fun record field -> RecordAccess (record, field))
    record acceses

let match_parser expr =
  let case = seq pattern (!(string "->") >>= fun _ -> expr) in
  string "match" >>= fun _ ->
  expr >>= fun expr ->
  !(string "with") >>= fun _ ->
  ( seq
      (!(char '|') |> opt >>= fun _ -> case)
      (!(char '|') >>= (fun _ -> case) |> many)
  <$> fun (c, cs) -> c :: cs )
  <$> fun cases -> Match (expr, cases)

let expr =
  makeRecParser (fun expr ->
      let basic_forms =
        makeRecParser (fun basic_forms ->
            !(choice
                [
                  parens_parser expr;
                  boolean_parser (fun b -> Boolean b);
                  (* number_parser (fun n -> Number n); *)
                  ident_parser (fun i -> Var i);
                  record expr;
                  variant_parser
                    (fun name p -> Constructor (name, p))
                    basic_forms;
                ]))
      in
      let application_parser =
        makeRecParser (fun application_parser ->
            record_acces_parser basic_forms >>= fun abs ->
            application_parser
            <$> (fun arg -> Application (abs, arg))
            <|> return abs)
      in
      let if_parser =
        makeRecParser (fun ifP -> if_parser ifP <|> application_parser)
      in
      !(choice
          [ if_parser; lambda_parser expr; match_parser expr; let_parser expr ]))

(* let let_parser = *)
(*   string "let" >>= fun _ -> *)
(*   opt !(string "rec") >>= fun _rec -> *)
(*   !pattern >>= fun ident -> *)
(*   !(char '=') >>= fun _ -> *)
(*   expr <$> fun e1 -> *)
(*   if Option.is_some _rec then RecBind (ident, e1) else Bind (ident, e1) *)
(* let top_level = expr <$> (fun e -> Expr e) <|> !let_parser *)
let parse =
  many1
    ( top_level >>= fun tl ->
      junk <$> fun _ -> tl )
  >> eof

(* >>>>>>> ml/main *)
let run = run_show
