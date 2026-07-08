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

type decl =
  | ConstDecl of string * expr
  | VarDecl of string * expr option

type stmt =
  | Block of stmt list
  | Empty
  | DeclStmt of decl list
  | Assign of string * expr
  | ExprStmt of expr
  | If of expr * stmt * stmt option
  | While of expr * stmt
  | Break
  | Continue
  | Return of expr option

type param = {
  param_type : typ;
  param_name : string;
}

type func = {
  return_type : typ;
  name : string;
  params : param list;
  body : stmt list;
}

type program_item =
  | GlobalDecl of decl list
  | FuncDef of func

type program = program_item list
