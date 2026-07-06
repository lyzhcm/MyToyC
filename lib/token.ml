type t =
  | Const
  | Int
  | Void
  | If
  | Else
  | While
  | Break
  | Continue
  | Return
  | Ident of string
  | Number of int
  | LParen
  | RParen
  | LBrace
  | RBrace
  | Semicolon
  | Comma
  | Assign
  | Plus
  | Minus
  | Star
  | Slash
  | Percent
  | Bang
  | Lt
  | Gt
  | Le
  | Ge
  | Eq
  | Ne
  | AndAnd
  | OrOr
  | Eof
