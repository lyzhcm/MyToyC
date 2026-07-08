module StringMap = Map.Make (String)

type instr =
  | Li of string * int
  | Mv of string * string
  | Addi of string * string * int
  | Lw of string * int * string
  | Sw of string * int * string
  | Add of string * string * string
  | Sub of string * string * string
  | Mul of string * string * string
  | Slli of string * string * int
  | Div of string * string * string
  | Rem of string * string * string
  | Slt of string * string * string
  | Xori of string * string * int
  | Seqz of string * string
  | Snez of string * string
  | And of string * string * string
  | Or of string * string * string
  | Neg of string * string
  | La of string * string
  | Call of string
  | Ret
  | Beqz of string * string
  | Jump of string

type program = {
  instrs : instr array;
  labels : int StringMap.t;
  data_labels : int StringMap.t;
  memory : (int, int64) Hashtbl.t;
}

let mask32 = Int64.shift_left 1L 32
let sign_bit32 = Int64.shift_left 1L 31

let normalize32 value =
  let value = Int64.rem value mask32 in
  let value = if value < 0L then Int64.add value mask32 else value in
  if value >= sign_bit32 then Int64.sub value mask32 else value

let split_once text ch =
  match String.index_opt text ch with
  | None -> (text, "")
  | Some index ->
      ( String.sub text 0 index,
        String.sub text (index + 1) (String.length text - index - 1) )

let parse_int text = int_of_string (String.trim text)

let parse_operands text =
  text |> String.split_on_char ',' |> List.map String.trim
  |> List.filter (fun part -> part <> "")

let parse_offset_base operand =
  match split_once operand '(' with
  | offset, base_with_paren ->
      let base_len = String.length base_with_paren in
      if base_len = 0 || base_with_paren.[base_len - 1] <> ')' then
        failwith ("invalid memory operand: " ^ operand);
      let base = String.sub base_with_paren 0 (base_len - 1) |> String.trim in
      (parse_int offset, base)

let parse_instruction line =
  let opcode, rest = split_once line ' ' in
  let operands = parse_operands rest in
  match (String.trim opcode, operands) with
  | "li", [ rd; imm ] -> Li (rd, parse_int imm)
  | "mv", [ rd; rs ] -> Mv (rd, rs)
  | "addi", [ rd; rs; imm ] -> Addi (rd, rs, parse_int imm)
  | "lw", [ rd; operand ] ->
      let offset, base = parse_offset_base operand in
      Lw (rd, offset, base)
  | "sw", [ rs; operand ] ->
      let offset, base = parse_offset_base operand in
      Sw (rs, offset, base)
  | "add", [ rd; rs1; rs2 ] -> Add (rd, rs1, rs2)
  | "sub", [ rd; rs1; rs2 ] -> Sub (rd, rs1, rs2)
  | "mul", [ rd; rs1; rs2 ] -> Mul (rd, rs1, rs2)
  | "slli", [ rd; rs; amount ] -> Slli (rd, rs, parse_int amount)
  | "div", [ rd; rs1; rs2 ] -> Div (rd, rs1, rs2)
  | "rem", [ rd; rs1; rs2 ] -> Rem (rd, rs1, rs2)
  | "slt", [ rd; rs1; rs2 ] -> Slt (rd, rs1, rs2)
  | "xori", [ rd; rs; imm ] -> Xori (rd, rs, parse_int imm)
  | "seqz", [ rd; rs ] -> Seqz (rd, rs)
  | "snez", [ rd; rs ] -> Snez (rd, rs)
  | "and", [ rd; rs1; rs2 ] -> And (rd, rs1, rs2)
  | "or", [ rd; rs1; rs2 ] -> Or (rd, rs1, rs2)
  | "neg", [ rd; rs ] -> Neg (rd, rs)
  | "la", [ rd; label ] -> La (rd, label)
  | "call", [ label ] -> Call label
  | "ret", [] -> Ret
  | "beqz", [ rs; label ] -> Beqz (rs, label)
  | "j", [ label ] -> Jump label
  | _ -> failwith ("unsupported instruction: " ^ line)

let parse assembly =
  let lines = String.split_on_char '\n' assembly in
  let section = ref `None in
  let pending_data_label = ref None in
  let next_data_addr = ref 4096 in
  let labels = ref StringMap.empty in
  let data_labels = ref StringMap.empty in
  let memory = Hashtbl.create 32 in
  let instrs = ref [] in
  let add_label label =
    labels := StringMap.add label (List.length !instrs) !labels
  in
  let add_data_word label value =
    let addr = !next_data_addr in
    next_data_addr := addr + 4;
    data_labels := StringMap.add label addr !data_labels;
    Hashtbl.replace memory addr (normalize32 (Int64.of_int value))
  in
  List.iter
    (fun raw_line ->
      let line = String.trim raw_line in
      if line <> "" then
        if line = ".data" then section := `Data
        else if line = ".text" then section := `Text
        else if String.length line >= 6 && String.sub line 0 6 = ".globl" then ()
        else if line.[String.length line - 1] = ':' then
          let label = String.sub line 0 (String.length line - 1) in
          match !section with
          | `Data -> pending_data_label := Some label
          | `Text -> add_label label
          | `None -> failwith ("label outside section: " ^ label)
        else if String.length line >= 5 && String.sub line 0 5 = ".word" then
          match !section, !pending_data_label with
          | `Data, Some label ->
              add_data_word label (parse_int (String.sub line 5 (String.length line - 5)));
              pending_data_label := None
          | _ -> failwith ("unexpected .word directive: " ^ line)
        else
          match !section with
          | `Text -> instrs := parse_instruction line :: !instrs
          | `Data | `None -> failwith ("unexpected line: " ^ line))
    lines;
  { instrs = Array.of_list (List.rev !instrs); labels = !labels; data_labels = !data_labels; memory }

type state = {
  regs : (string, int64) Hashtbl.t;
  memory : (int, int64) Hashtbl.t;
  mutable pc : int;
  mutable halted : bool;
  mutable result : int64;
}

let get_reg regs name =
  if name = "x0" || name = "zero" then 0L
  else Hashtbl.find_opt regs name |> Option.value ~default:0L

let set_reg regs name value =
  if name <> "x0" && name <> "zero" then
    Hashtbl.replace regs name (normalize32 value)

let get_mem memory address =
  Hashtbl.find_opt memory address |> Option.value ~default:0L

let set_mem memory address value =
  Hashtbl.replace memory address (normalize32 value)

let addr_of regs base offset =
  Int64.to_int (Int64.add (get_reg regs base) (Int64.of_int offset))

let label_pc program label =
  match StringMap.find_opt label program.labels with
  | Some pc -> pc
  | None -> failwith ("unknown code label: " ^ label)

let data_addr program label =
  match StringMap.find_opt label program.data_labels with
  | Some addr -> addr
  | None -> failwith ("unknown data label: " ^ label)

let binop regs rd rs1 rs2 op =
  set_reg regs rd (op (get_reg regs rs1) (get_reg regs rs2))

let run ?(max_steps = 1000000) assembly =
  let program = parse assembly in
  let regs = Hashtbl.create 32 in
  let memory = Hashtbl.copy program.memory in
  let halt_pc = -1 in
  let state =
    {
      regs;
      memory;
      pc = label_pc program "main";
      halted = false;
      result = 0L;
    }
  in
  set_reg regs "sp" 1048576L;
  set_reg regs "ra" (Int64.of_int halt_pc);
  let steps = ref 0 in
  while not state.halted do
    if !steps >= max_steps then failwith "simulation step limit exceeded";
    incr steps;
    if state.pc < 0 || state.pc >= Array.length program.instrs then
      failwith "program counter out of range";
    let next_pc = state.pc + 1 in
    let jump target = state.pc <- target in
    let advance () = state.pc <- next_pc in
    match program.instrs.(state.pc) with
    | Li (rd, imm) ->
        set_reg regs rd (Int64.of_int imm);
        advance ()
    | Mv (rd, rs) ->
        set_reg regs rd (get_reg regs rs);
        advance ()
    | Addi (rd, rs, imm) ->
        set_reg regs rd (Int64.add (get_reg regs rs) (Int64.of_int imm));
        advance ()
    | Lw (rd, offset, base) ->
        set_reg regs rd (get_mem memory (addr_of regs base offset));
        advance ()
    | Sw (rs, offset, base) ->
        set_mem memory (addr_of regs base offset) (get_reg regs rs);
        advance ()
    | Add (rd, rs1, rs2) ->
        binop regs rd rs1 rs2 Int64.add;
        advance ()
    | Sub (rd, rs1, rs2) ->
        binop regs rd rs1 rs2 Int64.sub;
        advance ()
    | Mul (rd, rs1, rs2) ->
        binop regs rd rs1 rs2 Int64.mul;
        advance ()
    | Slli (rd, rs, amount) ->
        set_reg regs rd (Int64.shift_left (get_reg regs rs) amount);
        advance ()
    | Div (rd, rs1, rs2) ->
        binop regs rd rs1 rs2 Int64.div;
        advance ()
    | Rem (rd, rs1, rs2) ->
        binop regs rd rs1 rs2 Int64.rem;
        advance ()
    | Slt (rd, rs1, rs2) ->
        set_reg regs rd
          (if get_reg regs rs1 < get_reg regs rs2 then 1L else 0L);
        advance ()
    | Xori (rd, rs, imm) ->
        set_reg regs rd (Int64.logxor (get_reg regs rs) (Int64.of_int imm));
        advance ()
    | Seqz (rd, rs) ->
        set_reg regs rd (if get_reg regs rs = 0L then 1L else 0L);
        advance ()
    | Snez (rd, rs) ->
        set_reg regs rd (if get_reg regs rs <> 0L then 1L else 0L);
        advance ()
    | And (rd, rs1, rs2) ->
        binop regs rd rs1 rs2 Int64.logand;
        advance ()
    | Or (rd, rs1, rs2) ->
        binop regs rd rs1 rs2 Int64.logor;
        advance ()
    | Neg (rd, rs) ->
        set_reg regs rd (Int64.neg (get_reg regs rs));
        advance ()
    | La (rd, label) ->
        set_reg regs rd (Int64.of_int (data_addr program label));
        advance ()
    | Call label ->
        set_reg regs "ra" (Int64.of_int next_pc);
        jump (label_pc program label)
    | Ret ->
        let target = Int64.to_int (get_reg regs "ra") in
        if target = halt_pc then (
          state.halted <- true;
          state.result <- get_reg regs "a0")
        else jump target
    | Beqz (rs, label) ->
        if get_reg regs rs = 0L then jump (label_pc program label) else advance ()
    | Jump label -> jump (label_pc program label)
  done;
  Int64.to_int state.result
