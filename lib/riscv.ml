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

let is_power_of_two value =
  value > 0 && value land (value - 1) = 0

let log2 value =
  let rec loop shift value =
    if value = 1 then shift else loop (shift + 1) (value lsr 1)
  in
  loop 0 value

let bit_positions value =
  let rec loop bit value acc =
    if value = 0 then List.rev acc
    else
      let acc = if value land 1 = 1 then bit :: acc else acc in
      loop (bit + 1) (value lsr 1) acc
  in
  loop 0 value []

let emit_shifted_term target source shift =
  if shift = 0 then emit_move target source
  else Printf.sprintf "  slli %s, %s, %d\n" target source shift

let strength_reduced_positive_mul target source imm =
  if is_power_of_two imm && log2 imm < 32 then
    Some (Printf.sprintf "  slli %s, %s, %d\n" target source (log2 imm))
  else
    let rec try_shift shift =
      if shift >= 31 then None
      else
        let power = 1 lsl shift in
        if imm = power + 1 then
          let shifted = if target = source then "t1" else target in
          Some
            (Printf.sprintf "  slli %s, %s, %d\n  add %s, %s, %s\n" shifted
               source shift target shifted source)
        else if imm = power - 1 then
          let shifted = if target = source then "t1" else target in
          Some
            (Printf.sprintf "  slli %s, %s, %d\n  sub %s, %s, %s\n" shifted
               source shift target shifted source)
        else try_shift (shift + 1)
    in
    match try_shift 1 with
    | Some _ as code -> code
    | None -> (
        match bit_positions imm with
        | [ first; second ] when second < 31 ->
            if target = source then
              Some
                (emit_shifted_term "t1" source first
                ^ emit_shifted_term "t2" source second
                ^ Printf.sprintf "  add %s, t1, t2\n" target)
            else
              Some
                (emit_shifted_term target source first
                ^ emit_shifted_term "t1" source second
                ^ Printf.sprintf "  add %s, %s, t1\n" target target)
        | _ -> None)

let strength_reduced_mul target source imm =
  match imm with
  | 0 -> Some (Printf.sprintf "  li %s, 0\n" target)
  | 1 -> Some (emit_move target source)
  | -1 -> Some (Printf.sprintf "  neg %s, %s\n" target source)
  | imm when imm > 0 -> strength_reduced_positive_mul target source imm
  | imm when imm <> Int32.to_int Int32.min_int -> (
      match strength_reduced_positive_mul target source (-imm) with
      | Some code -> Some (code ^ Printf.sprintf "  neg %s, %s\n" target target)
      | None -> None)
  | _ -> None

let save_area_size (allocation : Regalloc.allocation) use_frame_pointer =
  (List.length allocation.used_regs * 4) + 4
  + if use_frame_pointer then 4 else 0

let frame_size (allocation : Regalloc.allocation) use_frame_pointer =
  align_to 16
    ((allocation.stack_slots * 4) + save_area_size allocation use_frame_pointer)

let saved_reg_offset (allocation : Regalloc.allocation) use_frame_pointer index =
  frame_size allocation use_frame_pointer
  - (if use_frame_pointer then 12 else 8)
  - (index * 4)

let ra_offset (allocation : Regalloc.allocation) use_frame_pointer =
  frame_size allocation use_frame_pointer - 4

let s0_offset (allocation : Regalloc.allocation) use_frame_pointer =
  frame_size allocation use_frame_pointer - 8

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

let starts_with prefix text =
  let prefix_len = String.length prefix in
  String.length text >= prefix_len && String.sub text 0 prefix_len = prefix

let split_once text ch =
  match String.index_opt text ch with
  | None -> (text, "")
  | Some index ->
      ( String.sub text 0 index,
        String.sub text (index + 1) (String.length text - index - 1) )

let strip_trailing_newline text =
  let len = String.length text in
  if len > 0 && text.[len - 1] = '\n' then String.sub text 0 (len - 1)
  else text

let parse_memory_instr opcode line =
  let prefix = "  " ^ opcode ^ " " in
  if not (starts_with prefix line) then None
  else
    let rest =
      String.sub line (String.length prefix)
        (String.length line - String.length prefix)
    in
    let reg, mem = split_once rest ',' in
    let reg = String.trim reg in
    let mem = String.trim mem in
    if reg = "" || mem = "" then None else Some (reg, mem)

let parse_move_instr line =
  let prefix = "  mv " in
  if not (starts_with prefix line) then None
  else
    let rest =
      String.sub line (String.length prefix)
        (String.length line - String.length prefix)
    in
    let dest, source = split_once rest ',' in
    let dest = String.trim dest in
    let source = String.trim source in
    if dest = "" || source = "" then None else Some (dest, source)

let peephole_lines lines =
  let rec loop acc = function
    | line :: next :: rest -> (
        match (parse_move_instr line, parse_move_instr next) with
        | Some (dest, source), Some (next_dest, next_source)
          when dest = next_source && source = next_dest ->
            loop (line :: acc) rest
        | _ -> (
        match (parse_memory_instr "sw" line, parse_memory_instr "lw" next) with
        | Some (source, store_mem), Some (target, load_mem)
          when store_mem = load_mem ->
            let replacement =
              if source = target then []
              else [ emit_move target source |> strip_trailing_newline ]
            in
            loop (List.rev_append replacement (line :: acc)) rest
        | _ -> (
            match (parse_memory_instr "lw" line, parse_memory_instr "sw" next) with
            | Some (target, load_mem), Some (source, store_mem)
              when target = source && load_mem = store_mem ->
                loop (line :: acc) rest
            | _ -> loop (line :: acc) (next :: rest))))
    | line :: rest -> loop (line :: acc) rest
    | [] -> List.rev acc
  in
  loop [] lines

let peephole_asm asm =
  asm |> String.split_on_char '\n' |> peephole_lines |> String.concat "\n"

let emit_operand_to_a0 allocation operand = emit_load allocation "a0" operand

let result_target allocation dest fallback =
  match Regalloc.location allocation dest with
  | Regalloc.Phys phys -> phys
  | Regalloc.Stack _ -> fallback

let operand_reg allocation fallback = function
  | Ir.Imm value -> (Printf.sprintf "  li %s, %d\n" fallback value, fallback)
  | Ir.Reg reg -> (
      match Regalloc.location allocation reg with
      | Regalloc.Phys phys -> ("", phys)
      | Regalloc.Stack slot ->
          (emit_load_word fallback "s0" (slot_offset slot), fallback))

let emit_binop allocation dest op lhs rhs =
  let lhs_tmp = "t0" in
  let rhs_tmp = "t1" in
  let dest_tmp = result_target allocation dest "t2" in
  let store_result code = code ^ emit_store allocation dest_tmp dest in
  let emit_single operand instr =
    let operand_load, operand_reg = operand_reg allocation lhs_tmp operand in
    operand_load ^ instr dest_tmp operand_reg |> store_result
  in
  let min_i32 = Int32.to_int Int32.min_int in
  let max_i32 = Int32.to_int Int32.max_int in
  match (op, lhs, rhs) with
  | Ast.Add, operand, Ir.Imm imm | Ast.Add, Ir.Imm imm, operand ->
      emit_single operand (fun target source -> emit_addi target source imm)
  | Ast.Sub, operand, Ir.Imm imm when imm <> min_i32 ->
      emit_single operand (fun target source -> emit_addi target source (-imm))
  | Ast.Sub, Ir.Imm 0, operand ->
      emit_single operand (fun target source ->
          Printf.sprintf "  neg %s, %s\n" target source)
  | Ast.Eq, operand, Ir.Imm 0 | Ast.Eq, Ir.Imm 0, operand ->
      emit_single operand (fun target source ->
          Printf.sprintf "  seqz %s, %s\n" target source)
  | Ast.Ne, operand, Ir.Imm 0 | Ast.Ne, Ir.Imm 0, operand ->
      emit_single operand (fun target source ->
          Printf.sprintf "  snez %s, %s\n" target source)
  | Ast.Lt, operand, Ir.Imm imm when fits_imm12 imm ->
      emit_single operand (fun target source ->
          Printf.sprintf "  slti %s, %s, %d\n" target source imm)
  | Ast.Ge, operand, Ir.Imm imm when fits_imm12 imm ->
      emit_single operand (fun target source ->
          Printf.sprintf "  slti %s, %s, %d\n  xori %s, %s, 1\n" target
            source imm target target)
  | Ast.Le, operand, Ir.Imm imm when imm <> max_i32 && fits_imm12 (imm + 1) ->
      emit_single operand (fun target source ->
          Printf.sprintf "  slti %s, %s, %d\n" target source (imm + 1))
  | Ast.Gt, operand, Ir.Imm imm when imm <> max_i32 && fits_imm12 (imm + 1) ->
      emit_single operand (fun target source ->
          Printf.sprintf "  slti %s, %s, %d\n  xori %s, %s, 1\n" target
            source (imm + 1) target target)
  | Ast.Mul, operand, Ir.Imm imm | Ast.Mul, Ir.Imm imm, operand -> (
      let operand_load, operand_reg = operand_reg allocation lhs_tmp operand in
      match strength_reduced_mul dest_tmp operand_reg imm with
      | Some code -> operand_load ^ code |> store_result
      | None ->
          let rhs_load = Printf.sprintf "  li %s, %d\n" rhs_tmp imm in
          operand_load
          ^ rhs_load
          ^ Printf.sprintf "  mul %s, %s, %s\n" dest_tmp operand_reg rhs_tmp
          |> store_result)
  | Ast.LAnd, _, _ | Ast.LOr, _, _ ->
      let load = emit_load allocation lhs_tmp lhs ^ emit_load allocation rhs_tmp rhs in
      let instr =
        match op with
        | Ast.LAnd ->
            Printf.sprintf
              "  snez %s, %s\n  snez %s, %s\n  and %s, %s, %s\n" lhs_tmp
              lhs_tmp rhs_tmp rhs_tmp dest_tmp lhs_tmp rhs_tmp
        | Ast.LOr ->
            Printf.sprintf "  or %s, %s, %s\n  snez %s, %s\n" dest_tmp lhs_tmp
              rhs_tmp dest_tmp dest_tmp
        | _ -> ""
      in
      load ^ instr ^ emit_store allocation dest_tmp dest
  | _ ->
      let lhs_load, lhs_reg = operand_reg allocation lhs_tmp lhs in
      let rhs_load, rhs_reg = operand_reg allocation rhs_tmp rhs in
      let instr =
        match op with
        | Ast.Add -> Printf.sprintf "  add %s, %s, %s\n" dest_tmp lhs_reg rhs_reg
        | Ast.Sub -> Printf.sprintf "  sub %s, %s, %s\n" dest_tmp lhs_reg rhs_reg
        | Ast.Mul -> Printf.sprintf "  mul %s, %s, %s\n" dest_tmp lhs_reg rhs_reg
        | Ast.Div -> Printf.sprintf "  div %s, %s, %s\n" dest_tmp lhs_reg rhs_reg
        | Ast.Mod -> Printf.sprintf "  rem %s, %s, %s\n" dest_tmp lhs_reg rhs_reg
        | Ast.Lt -> Printf.sprintf "  slt %s, %s, %s\n" dest_tmp lhs_reg rhs_reg
        | Ast.Gt -> Printf.sprintf "  slt %s, %s, %s\n" dest_tmp rhs_reg lhs_reg
        | Ast.Le ->
            Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n" dest_tmp rhs_reg
              lhs_reg dest_tmp dest_tmp
        | Ast.Ge ->
            Printf.sprintf "  slt %s, %s, %s\n  xori %s, %s, 1\n" dest_tmp lhs_reg
              rhs_reg dest_tmp dest_tmp
        | Ast.Eq ->
            Printf.sprintf "  sub %s, %s, %s\n  seqz %s, %s\n" dest_tmp lhs_reg rhs_reg
              dest_tmp dest_tmp
        | Ast.Ne ->
            Printf.sprintf "  sub %s, %s, %s\n  snez %s, %s\n" dest_tmp lhs_reg rhs_reg
              dest_tmp dest_tmp
        | Ast.LAnd | Ast.LOr -> ""
      in
      lhs_load ^ rhs_load ^ instr ^ emit_store allocation dest_tmp dest

let emit_unop allocation dest op operand =
  let load, src = operand_reg allocation "t0" operand in
  let tmp = result_target allocation dest "t1" in
  let instr =
    match op with
    | Ast.Pos -> emit_move tmp src
    | Ast.Neg -> Printf.sprintf "  neg %s, %s\n" tmp src
    | Ast.LNot -> Printf.sprintf "  seqz %s, %s\n" tmp src
  in
  load ^ instr ^ emit_store allocation tmp dest

let emit_shift_left allocation dest operand amount =
  let operand_load, operand_reg = operand_reg allocation "t0" operand in
  let dest_tmp = result_target allocation dest "t1" in
  operand_load
  ^ Printf.sprintf "  slli %s, %s, %d\n" dest_tmp operand_reg amount
  ^ emit_store allocation dest_tmp dest

let emit_load_param allocation use_frame_pointer dest index =
  let target =
    match Regalloc.location allocation dest with
    | Regalloc.Phys phys -> phys
    | Regalloc.Stack _ -> "t0"
  in
  if index < 8 then
    emit_move target (Printf.sprintf "a%d" index) ^ emit_store allocation target dest
  else
    let offset = frame_size allocation use_frame_pointer + ((index - 8) * 4) in
    let base = if use_frame_pointer then "s0" else "sp" in
    emit_load_word target base offset ^ emit_store allocation target dest

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
  let operand_load, operand_reg = operand_reg allocation "t0" operand in
  emit_global_address "t1" name
  ^ operand_load
  ^ Printf.sprintf "  sw %s, 0(t1)\n" operand_reg

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

let emit_epilogue allocation use_frame_pointer =
  let frame_base = if use_frame_pointer then "s0" else "sp" in
  let restore_regs =
    allocation.used_regs
    |> List.mapi (fun index reg ->
           emit_load_word reg frame_base
             (saved_reg_offset allocation use_frame_pointer index))
    |> String.concat ""
  in
  let restore_s0 =
    if use_frame_pointer then
      emit_load_word "s0" "s0" (s0_offset allocation use_frame_pointer)
    else ""
  in
  restore_regs
  ^ emit_load_word "ra" frame_base (ra_offset allocation use_frame_pointer)
  ^ restore_s0
  ^ emit_addi "sp" "sp" (frame_size allocation use_frame_pointer)
  ^ "  ret\n"

let emit_return_a0 allocation use_frame use_frame_pointer =
  if not use_frame then "  ret\n"
  else emit_epilogue allocation use_frame_pointer

let emit_return allocation use_frame use_frame_pointer operand =
  if not use_frame then emit_operand_to_a0 allocation operand ^ "  ret\n"
  else
    emit_operand_to_a0 allocation operand
    ^ emit_epilogue allocation use_frame_pointer

let emit_move_instr allocation dest operand =
  match Regalloc.location allocation dest with
  | Regalloc.Phys phys -> emit_load allocation phys operand
  | Regalloc.Stack _ -> emit_load allocation "t0" operand ^ emit_store allocation "t0" dest

let operand_uses_reg reg = function
  | Ir.Imm _ -> false
  | Ir.Reg source -> source = reg

let instr_uses_reg reg = function
  | Ir.Move (_, operand) | Ir.Unary (_, _, operand)
  | Ir.ShiftLeft (_, operand, _) | Ir.StoreGlobal (_, operand)
  | Ir.BranchZero (operand, _) | Ir.Return operand ->
      operand_uses_reg reg operand
  | Ir.Binary (_, _, lhs, rhs) ->
      operand_uses_reg reg lhs || operand_uses_reg reg rhs
  | Ir.Call (_, _, args) -> List.exists (operand_uses_reg reg) args
  | Ir.LoadParam _ | Ir.LoadGlobal _ | Ir.Label _ | Ir.Jump _ -> false

let rec reg_used_later reg = function
  | [] -> false
  | instr :: rest -> instr_uses_reg reg instr || reg_used_later reg rest

let emit_branch_compare allocation op lhs rhs label =
  let emit_slti_branch operand imm branch_op =
    let load, reg = operand_reg allocation "t0" operand in
    load
    ^ Printf.sprintf "  slti t1, %s, %d\n  %s t1, zero, %s\n" reg imm
        branch_op label
  in
  match (op, lhs, rhs) with
  | Ast.Lt, operand, Ir.Imm imm when fits_imm12 imm ->
      emit_slti_branch operand imm "beq"
  | Ast.Le, operand, Ir.Imm imm when imm <> Int32.to_int Int32.max_int && fits_imm12 (imm + 1) ->
      emit_slti_branch operand (imm + 1) "beq"
  | Ast.Gt, operand, Ir.Imm imm when imm <> Int32.to_int Int32.max_int && fits_imm12 (imm + 1) ->
      emit_slti_branch operand (imm + 1) "bne"
  | Ast.Ge, operand, Ir.Imm imm when fits_imm12 imm ->
      emit_slti_branch operand imm "bne"
  | Ast.Eq, operand, Ir.Imm 0 | Ast.Eq, Ir.Imm 0, operand ->
      let load, reg = operand_reg allocation "t0" operand in
      load ^ Printf.sprintf "  bne %s, zero, %s\n" reg label
  | Ast.Ne, operand, Ir.Imm 0 | Ast.Ne, Ir.Imm 0, operand ->
      let load, reg = operand_reg allocation "t0" operand in
      load ^ Printf.sprintf "  beq %s, zero, %s\n" reg label
  | _ ->
      let lhs_load, lhs_reg = operand_reg allocation "t0" lhs in
      let rhs_load, rhs_reg = operand_reg allocation "t1" rhs in
      let branch =
        match op with
        | Ast.Lt -> Printf.sprintf "  bge %s, %s, %s\n" lhs_reg rhs_reg label
        | Ast.Gt -> Printf.sprintf "  bge %s, %s, %s\n" rhs_reg lhs_reg label
        | Ast.Le -> Printf.sprintf "  blt %s, %s, %s\n" rhs_reg lhs_reg label
        | Ast.Ge -> Printf.sprintf "  blt %s, %s, %s\n" lhs_reg rhs_reg label
        | Ast.Eq -> Printf.sprintf "  bne %s, %s, %s\n" lhs_reg rhs_reg label
        | Ast.Ne -> Printf.sprintf "  beq %s, %s, %s\n" lhs_reg rhs_reg label
        | _ -> ""
      in
      lhs_load ^ rhs_load ^ branch
let emit_instr allocation use_frame use_frame_pointer = function
  | Ir.LoadParam (dest, index) ->
      emit_load_param allocation use_frame_pointer dest index
  | Ir.Move (dest, operand) -> emit_move_instr allocation dest operand
  | Ir.Unary (dest, op, operand) -> emit_unop allocation dest op operand
  | Ir.Binary (dest, op, lhs, rhs) -> emit_binop allocation dest op lhs rhs
  | Ir.ShiftLeft (dest, operand, amount) ->
      emit_shift_left allocation dest operand amount
  | Ir.LoadGlobal (dest, name) -> emit_load_global allocation dest name
  | Ir.StoreGlobal (name, operand) -> emit_store_global allocation name operand
  | Ir.Call (dest, name, args) -> emit_call allocation dest name args
  | Ir.Label label -> Printf.sprintf "%s:\n" label
  | Ir.BranchZero (operand, label) ->
      let operand_load, operand_reg = operand_reg allocation "t0" operand in
      operand_load ^ Printf.sprintf "  beqz %s, %s\n" operand_reg label
  | Ir.Jump label -> Printf.sprintf "  j %s\n" label
  | Ir.Return operand -> emit_return allocation use_frame use_frame_pointer operand

let emit_instrs allocation use_frame use_frame_pointer body =
  let rec loop acc = function
    | Ir.LoadParam (dest, _) :: rest when not (reg_used_later dest rest) ->
        loop acc rest
    | Ir.Call (Some dest, name, args) :: Ir.Return (Ir.Reg result) :: rest
      when dest = result ->
        loop
          ( (emit_call allocation None name args
            ^ emit_return_a0 allocation use_frame use_frame_pointer)
            :: acc )
          rest
    | Ir.Binary (dest, op, lhs, rhs) :: Ir.BranchZero (Ir.Reg reg, label) :: rest
      when dest = reg
           && not (reg_used_later reg rest)
           && (match op with
              | Ast.Lt | Ast.Gt | Ast.Le | Ast.Ge | Ast.Eq | Ast.Ne -> true
              | _ -> false) ->
        loop (emit_branch_compare allocation op lhs rhs label :: acc) rest
    | instr :: rest ->
        loop (emit_instr allocation use_frame use_frame_pointer instr :: acc) rest
    | [] -> String.concat "" (List.rev acc)
  in
  loop [] body

let emit_global global =
  Printf.sprintf ".globl %s\n%s:\n  .word %d\n" (asm_symbol global.Ir.name) (asm_symbol global.name)
    global.init

let max_param_index body =
  List.fold_left
    (fun current -> function
      | Ir.LoadParam (_, index) -> max current index
      | _ -> current)
    (-1) body

let has_call body =
  List.exists
    (function
      | Ir.Call _ -> true
      | _ -> false)
    body

let can_omit_frame func allocation =
  allocation.Regalloc.stack_slots = 0
  && allocation.used_regs = []
  && max_param_index func.Ir.body < 8
  && not (has_call func.Ir.body)

let need_frame_pointer func allocation =
  allocation.Regalloc.stack_slots > 0 || max_param_index func.Ir.body >= 8

let emit_func func =
  let allocation = Regalloc.allocate func in
  let use_frame = not (can_omit_frame func allocation) in
  let use_frame_pointer = use_frame && need_frame_pointer func allocation in
  let prologue =
    if not use_frame then ""
    else
      let frame_size = frame_size allocation use_frame_pointer in
      let save_regs =
        allocation.used_regs
        |> List.mapi (fun index reg ->
               emit_store_word reg "sp"
                 (saved_reg_offset allocation use_frame_pointer index))
        |> String.concat ""
      in
      let save_s0 =
        if use_frame_pointer then
          emit_store_word "s0" "sp" (s0_offset allocation use_frame_pointer)
          ^ "  mv s0, sp\n"
        else ""
      in
      emit_addi "sp" "sp" (-frame_size)
      ^ emit_store_word "ra" "sp" (ra_offset allocation use_frame_pointer)
      ^ save_regs
      ^ save_s0
  in
  Printf.sprintf ".globl %s\n%s:\n%s%s" (asm_symbol func.Ir.name) (asm_symbol func.name) prologue
    (emit_instrs allocation use_frame use_frame_pointer func.body)
  |> peephole_asm

let emit_program (program : Ir.program) =
  let data_section =
    if program.globals = [] then ""
    else ".data\n" ^ (program.globals |> List.map emit_global |> String.concat "")
  in
  data_section ^ ".text\n" ^ (program.funcs |> List.map emit_func |> String.concat "\n")
