type typ =
  | TInt
  | TVoid

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Lt
  | Gt
  | Le
  | Ge
  | Eq
  | Ne
  | LAnd
  | LOr

type unop =
  | Pos
  | Neg
  | LNot

type expr =
  | Int of int
  | Var of string
  | Binary of binop * expr * expr
  | Unary of unop * expr
  | Call of string * expr list

type stmt =
  | Return of expr option

type func = {
  return_type : typ;
  name : string;
  body : stmt list;
}

type program = func list
