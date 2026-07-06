{
open Parser

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
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z' '_']
let ident = alpha (alpha | digit)*

rule token = parse
  | [' ' '\t' '\r' '\n'] { token lexbuf }
  | "//" [^ '\n' '\r']* { token lexbuf }
  | "/*" { block_comment lexbuf }
  | ident as name { keyword_or_ident name }
  | digit+ as n { NUMBER (int_of_string n) }
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
  | _ as c { failwith (Printf.sprintf "unexpected character: %c" c) }

and block_comment = parse
  | "*/" { token lexbuf }
  | eof { failwith "unterminated block comment" }
  | _ { block_comment lexbuf }
