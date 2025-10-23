open Types.Parsed
open Utils
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
  [
    "fun";
    "let";
    "rec";
    "in";
    "if";
    "then";
    "else";
    "match";
    "with";
    "type";
    "data";
  ]

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

let ignore_span x _ = x

let identifier_without_junk w =
  junk
  << spanned'
       (return w
       <*> (basic_identifier_without_junk |> tryP
           <|> (between (char '(') (junk << char ')') infix_identifier
               <?> "infix identifier")))

let identifier w = junk << identifier_without_junk w
let infix_identifier = infix_identifier

(* TODO: for infix too *)
let variant_identifier w = junk << char '`' << identifier_without_junk w
let variant_identifier_without_junk w = char '`' << identifier_without_junk w
let number_inner = takeWhile is_decimal
let number1_inner = takeWhile1 is_decimal

let number w =
  junk << spanned' (return w <*> (number1_inner <$> int_of_string)) <?> "number"

let float w =
  junk
  << spanned'
       (return w
       <*> (number1_inner
           >>= (fun first -> char '.' << number_inner <$> ( ^ ) (first ^ "."))
           <|> ( number_inner >>= fun first ->
                 char '.' << number1_inner <$> ( ^ ) (first ^ ".") )
           <$> float_of_string))
  <?> "float"

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

let unit w =
  junk
  << spanned'
       (return w <*> (char '(' << junk << char ')' <$> Fun.const () <?> "unit"))

let paren p = between (junk << char '(') (junk << char ')') p <?> "paren"

let record p identifier_short_hand assign w =
  let field =
    seq (identifier ignore_span) (junk << char assign << p)
    <$> fun (label, value) -> { label; value }
  in
  let field =
    match identifier_short_hand with
    | Some f ->
        field <|> identifier (fun label span -> { label; value = f label span })
    | None -> field
  in
  junk
  << spanned'
       (between (char '{')
          (junk << char '}')
          (return w
          <*> (p >> string "with" |> opt)
          <*> sepby field (junk << char ';')))
  <?> "record"

(* variant parser is only used for types so it won't be ambiguous with application parser *)
let constructor p zero w =
  junk
  << spanned'
       (return w
       <*> variant_identifier_without_junk ignore_span
       <*> (p <|> zero) <?> "constructor")

let nominal_constructor p w =
  junk
  << spanned'
       (return w <*> identifier_without_junk ignore_span <*> p <?> "constructor")

let rec typeP =
  Parser
    {
      unParse =
        (fun s ok err ->
          let basic_type =
            makeRecParser (fun basic_type ->
                return (fun _ty_p cons ->
                    List.fold_left
                      (fun ty con_name ->
                        TyCon { name = con_name; arguements = [ ty ] })
                      _ty_p cons)
                <*> choice
                      [
                        unit ignore_span <$> Fun.const TyUnit;
                        paren typeP;
                        return (fun _ty_p _ty ->
                            TyCon { name = _ty; arguements = _ty_p })
                        <*> paren (sepby1 basic_type (junk << char ','))
                        <*> identifier ignore_span;
                        junk << string "integer" <$> Fun.const TyInteger;
                        junk << string "float" <$> Fun.const TyFloat;
                        junk << string "string" <$> Fun.const TyString;
                        junk << string "boolean" <$> Fun.const TyBoolean;
                        record typeP None ':' (fun base row _ ->
                            TyRecord { fields = row; extends_record = base })
                        <?> "record";
                        (* type variables/constructors *)
                        identifier (fun _ty _ ->
                            TyCon { name = _ty; arguements = [] });
                      ]
                <*> many (identifier ignore_span))
          in
          let variant =
            between
              (junk << char '[')
              (junk << char ']')
              (sepby1
                 (seq
                    (variant_identifier ignore_span)
                    (opt basic_type <$> Option.value ~default:TyUnit))
                 (junk << char '|'))
            <$> List.map (fun (label, value) -> { label; value })
            <$> fun variants -> TyVariant { variants }
          in
          let functionP =
            variant <|> basic_type >>= fun domain ->
            opt (junk << string "->" << typeP)
            <$> Option.fold
                  ~some:(fun range -> TyArrow { domain; range })
                  ~none:domain
          in

          let (Parser { unParse }) = functionP in
          unParse s ok err);
    }

let ascription p f =
  spanned'
    (return (fun span expr -> Option.fold ~none:expr ~some:(f span expr)))
  <*> p
  <*> opt (junk << char ':' << typeP)

let type_variables =
  opt (between (junk << char '(') (junk << char ')') (many1 basic_identifier))
  <$> Option.map StringSet.of_list
  <$> Option.value ~default:StringSet.empty

let type_signature =
  spanned'
    (return (fun ty_variables name ty span ->
         TypeBind { name; ty_variables; ty; span })
    <*> (string "type" << type_variables)
    <*> basic_identifier
    <*> (junk << char '=' << typeP))

let nominal_type_signature =
  spanned'
    (return (fun ty_variables name ty span ->
         NominalTypeBind { name; ty_variables; ty; span; id = gensym_int () })
    <*> (string "data" << type_variables)
    <*> basic_identifier
    <*> (junk << char '=' << typeP))

let pattern =
  let record p =
    let field =
      seq (identifier ignore_span) (junk << char '=' << p)
      <$> fun (label, value) -> { label; value }
    in
    let field =
      field
      <|> identifier (fun ident span ->
              { label = ident; value = PVar { ident; span } })
    in
    junk
    << spanned'
         ( between (char '{') (junk << char '}') (sepby field (junk << char ';'))
         <$> fun fields span -> PRecord { fields; span } )
    <?> "record"
  in
  let stringP =
    junk
    << spanned'
         (return (fun value span -> PString { value; span })
         <*> (char '\"' << stringP >> char '\"'))
  in

  (* TODO: what is ascription's precedence *)
  let wildcard =
    junk << spanned (char '_') <$> fun { start; finish; _ } ->
    PWildcard { start; finish }
  in
  makeRecParser (fun pattern ->
      let basic =
        makeRecParser (fun basic ->
            choice
              [
                identifier (fun ident span -> PVar { ident; span });
                unit (fun _ span -> PUnit span);
                wildcard;
                paren
                  (ascription pattern (fun span pattern ty ->
                       PAscribe { span; pattern; ty }));
                stringP;
                float (fun value span -> Ast.PFloat { value; span });
                number (fun value span -> Ast.PInteger { value; span });
                constructor basic
                  (spanned' (return (fun span -> PUnit span)))
                  (fun name value span -> PConstructor { name; value; span });
                (* we dont do shorthand for nominal records as that would mean any pattern variable would automatically be nominal constructor - so we want to be consistent between patterns and data declarations *)
                (* if we would want to be consitent we would also want to make expression/pattern have shorthand *)
                (* which we be problem especilaly for expression where we use function to represent nominal constructor (but i guess if we mark it as such instead of turning it into function we could just make the variable representing this constructor just be the Constructor term itself *)
                (* for patterns whe would also need to lookup for vars if there are any constructors with that name *)
                nominal_constructor basic (fun name value span ->
                    PNominalConstructor { name; value; span });
                record pattern;
              ])
      in
      let asP =
        spanned'
          (return (fun value ->
               Option.fold
                 ~some:(fun name span -> PAs { name; value; span })
                 ~none:(fun _ -> value))
          <*> basic
          <*> (junk << string "as" << identifier ignore_span |> opt))
      in
      (* maybe the asP should come after or not before *)
      spanned'
        ( sepby1 asP (junk << char '|') <$> function
          | [ p ] -> fun _ -> p
          | patterns -> fun span -> POr { patterns; span } ))

let unless b p = if b then return None else p <$> fun x -> Some x
let whenP b p = if b then p <$> fun x -> Some x else return None
let fun_params = many pattern
let fun_params1 = many1 pattern

let let_head is_rec expr =
  let expr = junk << char '=' << expr in
  let function_signature =
    seq
      (identifier (fun ident span -> PVar { ident; span }))
      (spanned'
         (return (fun parameters e span ->
              Lambda { parameters; body = e; span })
         <*> fun_params1 <*> expr))
  in
  let plain_let = seq pattern expr in
  string "let"
  << whenP is_rec (junk << string "rec")
  << (function_signature <|> plain_let)

let let_head_no_junk is_rec expr = junk << let_head is_rec expr

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
                  paren
                    (ascription (expr false) (fun span value ty ->
                         Ascribe { span; value; ty }))
                  >> last_quote is_end;
                  junk << char '\"' <?> "start of string"
                  << spanned'
                       (return (fun value span -> String { value; span })
                       <*> check
                             (* make sure that last expression is not string starting with newline *)
                             (*TODO: maybe only do this if in application*)
                             !->(String.starts_with ~prefix:"\n")
                             stringP)
                  >> unless is_end (char '\"' <?> "end of expression");
                  float (fun value span -> Ast.Float { value; span })
                  >> last_quote is_end;
                  (* TODO: for construction should a "constructor" be no different than an application, meaning that each constructor is a n-ary function, that can be destructed into its values, would also have to update type parsing to handle this *)
                  constructor (basic_expr is_end)
                    (spanned' (return (fun span -> Unit span))
                    >> last_quote is_end)
                    (fun name value span -> Constructor { name; value; span })
                  >> last_quote is_end;
                  number (fun value span -> Ast.Integer { value; span })
                  >> last_quote is_end;
                  identifier (fun ident span -> Var { ident; span })
                  >> last_quote is_end;
                  unit (fun _ span -> Unit span) >> last_quote is_end;
                  record (expr false)
                    (Some (fun ident span -> Var { ident; span }))
                    '='
                    (fun record new_fields ->
                      Option.fold
                        ~some:(fun record span ->
                          RecordExtend { record; new_fields; span })
                        ~none:(fun span ->
                          Ast.Record { fields = new_fields; span })
                        record)
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
      << identifier (fun projector span record ->
             let span' = span_of_expr record in
             RecordAccess
               { record; projector; span = Utils.combine_spans span' span }))
    <$> List.fold_left ( |> ) value
    >> last_quote is_end)
    <|> basic_expr is_end
  in
  let application is_end =
    if is_end then
      let rec go func =
        let get_func func arguement =
          Option.fold ~none:arguement
            ~some:(fun lambda ->
              let span = span_of_expr lambda in
              let span' = span_of_expr arguement in
              Application
                { lambda; arguement; span = Utils.combine_spans span span' })
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
            (fun lambda arguement ->
              let span = span_of_expr lambda in
              let span' = span_of_expr arguement in
              Application
                { lambda; arguement; span = Utils.combine_spans span span' })
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
              spanned'
                ( seq
                    (junk << string "if" << expr false)
                    (seq
                       (junk << string "then" << expr false)
                       (junk << string "else" << expr is_end))
                <$> fun (condition, (consequent, alternative)) span ->
                  If { condition; consequent; alternative; span } )
            in
            unParse s ok err);
      }
  in
  let funP expr =
    spanned'
      ( seq (junk << string "fun" << fun_params >> (junk << string "->")) expr
      <$> fun (parameters, body) span -> Lambda { parameters; body; span } )
  in
  let letP expr is_end =
    let endP = junk << string "in" << expr is_end in
    junk
    << spanned'
         (return (fun (name, e1) e2 span -> LetRec { name; e1; e2; span })
         <*> let_head_no_junk true (expr false)
         <*> endP
         <|> (return (fun (name, e1) e2 span -> Let { name; e1; e2; span })
             <*> let_head false (expr false)
             <*> endP))
  in

  let case expr is_end =
    let case is_end =
      (* TODO: multi or pattern *)
      seq (junk << pattern) (junk << string "->" << expr is_end)
      <$> fun (pattern, result) -> { pattern; result }
    in
    junk
    << spanned'
         ( string "match" << junk << expr false >> junk >> string "with"
         >>= fun value ->
           (if is_end then
              let end_cases =
                makeRecParser (fun parser ->
                    choice
                      [
                        return List.cons
                        <*> (junk << char '|' << case false)
                        <*> parser;
                        ( junk << char '|' << case true <$> fun end_case ->
                          [ end_case ] );
                      ])
              in
              seq (junk << char '|' |> opt << case false) end_cases
              <$> (fun (c, cases) -> c :: cases)
              <|> ( junk << char '|' |> opt << case is_end <$> fun case ->
                    [ case ] )
            else
              seq
                (junk << char '|' |> opt << case false)
                (junk << char '|' << case false |> many)
              <$> fun (c, cs) -> c :: cs)
           <$> fun cases span -> Match { value; cases; span } )
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
  spanned'
    (let_head true (expr true)
    <$> (fun (name, value) span -> RecBind { name; value; span })
    <|> ( let_head false (expr true) <$> fun (name, value) span ->
          Bind { name; value; span } ))

let top_level =
  char '\"'
  << choice (* TODO: maybe allow mutliple top level term in single quotes *)
       [
         letP;
         (expr true <$> fun expr -> Expr expr);
         (* TODO: maybe consume new line *)
         type_signature >> junk >> char '\"';
         nominal_type_signature >> junk >> char '\"';
       ]
  <|> (stringP1 <?> "top level string" <$> fun string -> Ast.PrintString string)

let parse = many1 top_level >> eof
let run = run_show
