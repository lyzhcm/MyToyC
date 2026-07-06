{
open Parser

let fail_at lexbuf message =
  let pos = Lexing.lexeme_start_p lexbuf in
  failwith (Printf.sprintf "%s at line %d, column %d" message pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1))

let keyword_or_ident = function
  | "const" -> CONST
  | "int" -> INT
  | "void" -> VOID
  | "if" -> IF
  | "else" -> ELSE
  | "while" -> WHILE
  | "break" -> BREAK
  | "continue" -> CONTINUE
  | "return" -> RETURN
  | name -> IDENT name

let digit_value = function
  | '0' .. '9' as c -> Char.code c - Char.code '0'
  | 'a' .. 'f' as c -> 10 + Char.code c - Char.code 'a'
  | 'A' .. 'F' as c -> 10 + Char.code c - Char.code 'A'
  | _ -> invalid_arg "digit_value"

let parse_based_int base start text =
  let value = ref 0 in
  for i = start to String.length text - 1 do
    value := (!value * base) + digit_value text.[i]
  done;
  !value

let parse_number text =
  let len = String.length text in
  if len >= 2 && text.[0] = '0' && (text.[1] = 'x' || text.[1] = 'X') then
    parse_based_int 16 2 text
  else if len > 1 && text.[0] = '0' then
    parse_based_int 8 1 text
  else
    int_of_string text
}

let digit = ['0'-'9']
let oct_digit = ['0'-'7']
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let alpha = ['a'-'z' 'A'-'Z' '_']
let ident = alpha (alpha | digit)*
let decimal = ['1'-'9'] digit*
let octal = '0' oct_digit*
let hexadecimal = '0' ['x' 'X'] hex_digit+

rule token = parse
  | [' ' '\t' '\r'] { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "//" { line_comment lexbuf }
  | "/*" { block_comment lexbuf }
  | ident as name { keyword_or_ident name }
  | hexadecimal as n { NUMBER (parse_number n) }
  | octal as n { NUMBER (parse_number n) }
  | decimal as n { NUMBER (parse_number n) }
  | "&&" { AND_AND }
  | "||" { OR_OR }
  | "<=" { LE }
  | ">=" { GE }
  | "==" { EQ }
  | "!=" { NE }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ';' { SEMICOLON }
  | ',' { COMMA }
  | '=' { ASSIGN }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { STAR }
  | '/' { SLASH }
  | '%' { PERCENT }
  | '!' { BANG }
  | '<' { LT }
  | '>' { GT }
  | eof { EOF }
  | _ as c { fail_at lexbuf (Printf.sprintf "unexpected character: %c" c) }

and line_comment = parse
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { line_comment lexbuf }

and block_comment = parse
  | "*/" { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; block_comment lexbuf }
  | eof { fail_at lexbuf "unterminated block comment" }
  | _ { block_comment lexbuf }
