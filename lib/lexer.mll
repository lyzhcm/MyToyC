{
open Parser

let fail_at lexbuf message =
  let pos = Lexing.lexeme_start_p lexbuf in
  Diagnostic.fail
    (Printf.sprintf "%s at line %d, column %d" message pos.pos_lnum
       (pos.pos_cnum - pos.pos_bol + 1))

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

let parse_number = int_of_string
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z' '_']
let ident = alpha (alpha | digit)*
let decimal = '0' | ['1'-'9'] digit*
let leading_zero_decimal = '0' digit+
let hexadecimal = '0' ['x' 'X'] (digit | ['a'-'f' 'A'-'F'])+

rule token = parse
  | [' ' '\t' '\r'] { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "//" { line_comment lexbuf }
  | "/*" { block_comment lexbuf }
  | ident as name { keyword_or_ident name }
  | hexadecimal { fail_at lexbuf "hexadecimal integer literals are not allowed; NUMBER must be decimal" }
  | leading_zero_decimal { fail_at lexbuf "decimal integer literals cannot have leading zeros" }
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
