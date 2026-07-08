let align_to alignment value =
  if value = 0 then 0 else ((value + alignment - 1) / alignment) * alignment

let slot_offset slot = slot * 4

let asm_symbol name =
  if name = "main" then name else "__mytoyc_" ^ name
let fits_imm12 value = value >= -2048 && value <= 2047

let emit_addi rd rs imm =
  if imm = 0 then ""
  else if fits_imm12 imm then Printf.sprintf "  addi %s, %s, %d\n" rd rs imm
  else Printf.sprintf "  li t6, %d\n  add %s, %s, t6\n" imm rd rs

let emit_load_word target base offset =
  if fits_imm12 offset then Printf.sprintf "  lw %s, %d(%s)\n" target offset base
  else
    Printf.sprintf "  li t6, %d\n  add t6, %s, t6\n  lw %s, 0(t6)\n" offset base target

let emit_store_word source base offset =
  if fits_imm12 offset then Printf.sprintf "  sw %s, %d(%s)\n" source offset base
  else
    Printf.sprintf "  li t6, %d\n  add t6, %s, t6\n  sw %s, 0(t6)\n" offset base source
let emit_move target source =
  if target = source then "" else Printf.sprintf "  mv %s, %s\n" target source

let save_area_size (allocation : Regalloc.allocation) =
  (List.length allocation.used_regs * 4) + 8

let frame_size (allocation : Regalloc.allocation) =
  align_to 16 ((allocation.stack_slots * 4) + save_area_size allocation)

let saved_reg_offset (allocation : Regalloc.allocation) index =
  frame_size allocation - 12 - (index * 4)

let ra_offset (allocation : Regalloc.allocation) = frame_size allocation - 4

let s0_offset (allocation : Regalloc.allocation) = frame_size allocation - 8

let emit_load allocation target = function
  | Ir.Imm value -> Printf.sprintf "  li %s, %d\n" target value
  | Ir.Reg reg -> (
      match Regalloc.location allocation reg with
      | Regalloc.Phys phys -> emit_move target phys
      | Regalloc.Stack slot ->
          emit_load_word target "s0" (slot_offset slot))

let emit_store allocation source reg =
  match Regalloc.location allocation reg with
  | Regalloc.Phys phys -> emit_move phys source
  | Regalloc.Stack slot ->
      emit_store_word source "s0" (slot_offset slot)

let emit_operand_to_a0 allocation operand = emit_load allocation "a0" operand

let result_target allocation dest fallback =
  match Regalloc.location allocation dest with
  | Regalloc.Phys phys -> phys
  | Regalloc.Stack _ -> fallback

let emit_binop allocation dest op lhs rhs =
  let lhs_tmp = "t0" in
  let rhs_tmp = "t1" in
  let dest_tmp = result_target allocation dest "t2" in
  let load = emit_load allocation lhs_tmp lhs ^ emit_load allocation rhs_tmp rhs in
  let instr =
    match op with
    | Ast.Add -> Printf.sprintf "  add %s, %s, %s\n" dest_tmp lhs_tmp rhs_tmp
    | Ast.Sub -> Printf.sprintf "  sub %s, %s, %s\n" dest_tmp lhs_tmp rhs_tmp
    | Ast.Mul -> Printf.sprintf "  mul %s, %s, %s\n" dest_tmp lhs_tmp rhs_tmp
    | Ast.Div -> Printf.sprintf "  div %s, %s, %s\n" dest_tmp lhs_tmp rhs_tmp
    | Ast.Mod -> Printf.sprintf "  rem %s, %s, %s\n" dest_tmp lhs_tmp rhs_tmp
    | Ast.Lt -> Printf.sprintf "  slt %s, %s, %s\n" dest_tmp lhs_tmp rhs_tmp
    | Ast.Gt -> Printf.sprintf "  slt %s, %s, %s\n" dest_tmp rhs_tmp lhs_tmp
    | Ast.Le ->
        Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n" dest_tmp rhs_tmp
          lhs_tmp dest_tmp dest_tmp
    | Ast.Ge ->
        Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n" dest_tmp lhs_tmp
          rhs_tmp dest_tmp dest_tmp
    | Ast.Eq ->
        Printf.sprintf "  sub %s, %s, %s\n  seqz %s, %s\n" dest_tmp lhs_tmp rhs_tmp
          dest_tmp dest_tmp
    | Ast.Ne ->
        Printf.sprintf "  sub %s, %s, %s\n  snez %s, %s\n" dest_tmp lhs_tmp rhs_tmp
          dest_tmp dest_tmp
    | Ast.LAnd ->
        Printf.sprintf
          "  snez %s, %s\n  snez %s, %s\n  and %s, %s, %s\n" lhs_tmp lhs_tmp
          rhs_tmp rhs_tmp dest_tmp lhs_tmp rhs_tmp
    | Ast.LOr ->
        Printf.sprintf
          "  or %s, %s, %s\n  snez %s, %s\n" dest_tmp lhs_tmp rhs_tmp dest_tmp
          dest_tmp
  in
  load ^ instr ^ emit_store allocation dest_tmp dest

let emit_unop allocation dest op operand =
  let tmp = result_target allocation dest "t0" in
  let load = emit_load allocation tmp operand in
  let instr =
    match op with
      | Ast.Pos -> Printf.sprintf "  mv %s, %s\n" tmp tmp
      | Ast.Neg -> Printf.sprintf "  neg %s, %s\n" tmp tmp
      | Ast.LNot -> Printf.sprintf "  seqz %s, %s\n" tmp tmp
  in
  load ^ instr ^ emit_store allocation tmp dest

let emit_shift_left allocation dest operand amount =
  let operand_tmp = "t0" in
  let dest_tmp = result_target allocation dest "t1" in
  emit_load allocation operand_tmp operand
  ^ Printf.sprintf "  slli %s, %s, %d\n" dest_tmp operand_tmp amount
  ^ emit_store allocation dest_tmp dest

let emit_load_param allocation dest index =
  let target =
    match Regalloc.location allocation dest with
    | Regalloc.Phys phys -> phys
    | Regalloc.Stack _ -> "t0"
  in
  if index < 8 then
    Printf.sprintf "  mv %s, a%d\n%s" target index
      (emit_store allocation target dest)
  else
    let offset = frame_size allocation + ((index - 8) * 4) in
    emit_load_word target "s0" offset ^ emit_store allocation target dest

let emit_global_address tmp name =
  Printf.sprintf "  la %s, %s\n" tmp (asm_symbol name)

let emit_load_global allocation dest name =
  let target =
    match Regalloc.location allocation dest with
    | Regalloc.Phys phys -> phys
    | Regalloc.Stack _ -> "t1"
  in
  emit_global_address "t0" name ^ Printf.sprintf "  lw %s, 0(t0)\n" target
  ^ emit_store allocation target dest

let emit_store_global allocation name operand =
  emit_global_address "t1" name
  ^ emit_load allocation "t0" operand
  ^ "  sw t0, 0(t1)\n"

let emit_call allocation dest name args =
  let stack_arg_count = max 0 (List.length args - 8) in
  let stack_arg_bytes = align_to 16 (stack_arg_count * 4) in
  let setup_stack =
    if stack_arg_bytes = 0 then ""
    else emit_addi "sp" "sp" (-stack_arg_bytes)
  in
  let setup_args =
    args
    |> List.mapi (fun index operand ->
           if index < 8 then
             emit_load allocation (Printf.sprintf "a%d" index) operand
           else
             let offset = (index - 8) * 4 in
             emit_load allocation "t0" operand
             ^ emit_store_word "t0" "sp" offset)
    |> String.concat ""
  in
  let cleanup_stack =
    if stack_arg_bytes = 0 then ""
    else emit_addi "sp" "sp" stack_arg_bytes
  in
  let save_result =
    match dest with
    | None -> ""
    | Some reg -> emit_store allocation "a0" reg
  in
  setup_stack ^ setup_args ^ Printf.sprintf "  call %s\n" (asm_symbol name) ^ cleanup_stack
  ^ save_result

let emit_return allocation operand =
  let restore_regs =
    allocation.used_regs
    |> List.mapi (fun index reg ->
           emit_load_word reg "s0" (saved_reg_offset allocation index))
    |> String.concat ""
  in
  emit_operand_to_a0 allocation operand
  ^ restore_regs
  ^ emit_load_word "ra" "s0" (ra_offset allocation)
  ^ emit_load_word "s0" "s0" (s0_offset allocation)
  ^ emit_addi "sp" "sp" (frame_size allocation)
  ^ "  ret\n"

let emit_instr allocation = function
  | Ir.LoadParam (dest, index) -> emit_load_param allocation dest index
  | Ir.Move (dest, operand) ->
      emit_load allocation "t0" operand ^ emit_store allocation "t0" dest
  | Ir.Unary (dest, op, operand) -> emit_unop allocation dest op operand
  | Ir.Binary (dest, op, lhs, rhs) -> emit_binop allocation dest op lhs rhs
  | Ir.ShiftLeft (dest, operand, amount) ->
      emit_shift_left allocation dest operand amount
  | Ir.LoadGlobal (dest, name) -> emit_load_global allocation dest name
  | Ir.StoreGlobal (name, operand) -> emit_store_global allocation name operand
  | Ir.Call (dest, name, args) -> emit_call allocation dest name args
  | Ir.Label label -> Printf.sprintf "%s:\n" label
  | Ir.BranchZero (operand, label) ->
      emit_load allocation "t0" operand ^ Printf.sprintf "  beqz t0, %s\n" label
  | Ir.Jump label -> Printf.sprintf "  j %s\n" label
  | Ir.Return operand -> emit_return allocation operand

let emit_global global =
  Printf.sprintf ".globl %s\n%s:\n  .word %d\n" (asm_symbol global.Ir.name) (asm_symbol global.name)
    global.init

let emit_func func =
  let allocation = Regalloc.allocate func in
  let frame_size = frame_size allocation in
  let save_regs =
    allocation.used_regs
    |> List.mapi (fun index reg ->
           emit_store_word reg "sp" (saved_reg_offset allocation index))
    |> String.concat ""
  in
  let prologue =
    emit_addi "sp" "sp" (-frame_size)
    ^ emit_store_word "ra" "sp" (ra_offset allocation)
    ^ emit_store_word "s0" "sp" (s0_offset allocation)
    ^ save_regs
    ^ "  mv s0, sp\n"
  in
  Printf.sprintf ".globl %s\n%s:\n%s%s" (asm_symbol func.Ir.name) (asm_symbol func.name) prologue
    (func.body |> List.map (emit_instr allocation) |> String.concat "")

let emit_program (program : Ir.program) =
  let data_section =
    if program.globals = [] then ""
    else ".data\n" ^ (program.globals |> List.map emit_global |> String.concat "")
  in
  data_section ^ ".text\n" ^ (program.funcs |> List.map emit_func |> String.concat "\n")
