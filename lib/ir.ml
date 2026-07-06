type vreg = int

type operand =
  | Imm of int
  | Reg of vreg

type instr =
  | Move of vreg * operand
  | Unary of vreg * Ast.unop * operand
  | Binary of vreg * Ast.binop * operand * operand
  | Return of operand

type func = {
  name : string;
  body : instr list;
}

type program = func list
