let reg_name reg =
  if reg < 5 then Printf.sprintf "t%d" reg
  else
    Diagnostic.fail
      "too many temporary registers for this simple RISC-V backend"

let emit_load target = function
  | Ir.Imm value -> Printf.sprintf "  li %s, %d\n" target value
  | Ir.Reg reg -> Printf.sprintf "  mv %s, %s\n" target (reg_name reg)

let emit_operand_to_a0 operand = emit_load "a0" operand

let emit_binop dest op lhs rhs =
  let dest = reg_name dest in
  let lhs_tmp = "t5" in
  let rhs_tmp = "t6" in
  let load = emit_load lhs_tmp lhs ^ emit_load rhs_tmp rhs in
  let instr =
    match op with
    | Ast.Add -> Printf.sprintf "  add %s, %s, %s\n" dest lhs_tmp rhs_tmp
    | Ast.Sub -> Printf.sprintf "  sub %s, %s, %s\n" dest lhs_tmp rhs_tmp
    | Ast.Mul -> Printf.sprintf "  mul %s, %s, %s\n" dest lhs_tmp rhs_tmp
    | Ast.Div -> Printf.sprintf "  div %s, %s, %s\n" dest lhs_tmp rhs_tmp
    | Ast.Mod -> Printf.sprintf "  rem %s, %s, %s\n" dest lhs_tmp rhs_tmp
    | Ast.Lt -> Printf.sprintf "  slt %s, %s, %s\n" dest lhs_tmp rhs_tmp
    | Ast.Gt -> Printf.sprintf "  slt %s, %s, %s\n" dest rhs_tmp lhs_tmp
    | Ast.Le ->
        Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n" dest rhs_tmp
          lhs_tmp dest dest
    | Ast.Ge ->
        Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n" dest lhs_tmp
          rhs_tmp dest dest
    | Ast.Eq ->
        Printf.sprintf "  sub %s, %s, %s\n  seqz %s, %s\n" dest lhs_tmp rhs_tmp
          dest dest
    | Ast.Ne ->
        Printf.sprintf "  sub %s, %s, %s\n  snez %s, %s\n" dest lhs_tmp rhs_tmp
          dest dest
    | Ast.LAnd ->
        Printf.sprintf
          "  snez %s, %s\n  snez %s, %s\n  and %s, %s, %s\n" lhs_tmp lhs_tmp
          rhs_tmp rhs_tmp dest lhs_tmp rhs_tmp
    | Ast.LOr ->
        Printf.sprintf
          "  or %s, %s, %s\n  snez %s, %s\n" dest lhs_tmp rhs_tmp dest dest
  in
  load ^ instr

let emit_unop dest op operand =
  let dest = reg_name dest in
  let tmp = "t6" in
  let load = emit_load tmp operand in
  let instr =
    match op with
    | Ast.Pos -> Printf.sprintf "  mv %s, %s\n" dest tmp
    | Ast.Neg -> Printf.sprintf "  neg %s, %s\n" dest tmp
    | Ast.LNot -> Printf.sprintf "  seqz %s, %s\n" dest tmp
  in
  load ^ instr

let emit_instr = function
  | Ir.Move (dest, operand) -> emit_load (reg_name dest) operand
  | Ir.Unary (dest, op, operand) -> emit_unop dest op operand
  | Ir.Binary (dest, op, lhs, rhs) -> emit_binop dest op lhs rhs
  | Ir.Return operand -> emit_operand_to_a0 operand ^ "  ret\n"

let emit_func func =
  Printf.sprintf ".globl %s\n%s:\n%s" func.Ir.name func.name
    (func.body |> List.map emit_instr |> String.concat "")

let emit_program (program : Ir.program) =
  ".text\n" ^ (program |> List.map emit_func |> String.concat "\n")
