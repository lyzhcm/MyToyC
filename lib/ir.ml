type vreg = int

type operand =
  | Imm of int
  | Reg of vreg

type instr =
  | LoadParam of vreg * int
  | Move of vreg * operand
  | Unary of vreg * Ast.unop * operand
  | Binary of vreg * Ast.binop * operand * operand
  | ShiftLeft of vreg * operand * int
  | LoadGlobal of vreg * string
  | StoreGlobal of string * operand
  | Call of vreg option * string * operand list
  | Label of string
  | BranchZero of operand * string
  | Jump of string
  | Return of operand

type func = {
  name : string;
  body : instr list;
}

type global = {
  name : string;
  init : int;
}

type program = {
  globals : global list;
  funcs : func list;
}
