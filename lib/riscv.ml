let emit_operand = function
  | Ir.Imm value -> Printf.sprintf "li a0, %d" value
  | Ir.Reg reg -> Printf.sprintf "mv a0, t%d" reg

let emit_instr = function
  | Ir.Return operand ->
      Printf.sprintf "  %s\n  ret\n" (emit_operand operand)

let emit_func func =
  Printf.sprintf ".globl %s\n%s:\n%s" func.Ir.name func.name
    (func.body |> List.map emit_instr |> String.concat "")

let emit_program (program : Ir.program) =
  ".text\n" ^ (program |> List.map emit_func |> String.concat "\n")
