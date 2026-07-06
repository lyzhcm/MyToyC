type vreg = int

type operand =
  | Imm of int
  | Reg of vreg

type instr =
  | Return of operand

type func = {
  name : string;
  body : instr list;
}

type program = func list
