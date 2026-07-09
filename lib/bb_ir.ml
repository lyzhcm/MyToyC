module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

type label = string

type terminator =
  | Return of Ir.operand
  | Jump of label
  | BranchZero of Ir.operand * label * label option
  | BranchCmp of Ast.binop * Ir.operand * Ir.operand * label * label option
  | Unreachable

type block = {
  label : label;
  instrs : Ir.instr list;
  terminator : terminator;
}

type func = {
  name : string;
  entry : label;
  blocks : block list;
}

let entry_label name = ".L_" ^ name ^ "_entry"

let fresh_label name purpose counter =
  let label = Printf.sprintf ".L_%s_%s_%d" name purpose !counter in
  incr counter;
  label

let terminator_successors = function
  | Return _ | Unreachable -> []
  | Jump label -> [ label ]
  | BranchZero (_, zero_label, None) -> [ zero_label ]
  | BranchZero (_, zero_label, Some nonzero_label) ->
      [ zero_label; nonzero_label ]
  | BranchCmp (_, _, _, zero_label, None) -> [ zero_label ]
  | BranchCmp (_, _, _, zero_label, Some nonzero_label) ->
      [ zero_label; nonzero_label ]

let operand_uses = function
  | Ir.Imm _ -> []
  | Ir.Reg reg -> [ reg ]

let terminator_uses = function
  | Return operand -> operand_uses operand
  | BranchZero (operand, _, _) -> operand_uses operand
  | BranchCmp (_, lhs, rhs, _, _) -> operand_uses lhs @ operand_uses rhs
  | Jump _ | Unreachable -> []

let is_control = function
  | Ir.Label _ | Ir.BranchZero _ | Ir.Jump _ | Ir.Return _ -> true
  | _ -> false

let block_map blocks =
  List.fold_left
    (fun blocks block -> StringMap.add block.label block blocks)
    StringMap.empty blocks

let referenced_labels func =
  List.fold_left
    (fun labels block ->
      block.terminator
      |> terminator_successors
      |> List.fold_left (fun labels label -> StringSet.add label labels) labels)
    StringSet.empty func.blocks

let of_ir_func (func : Ir.func) =
  let counter = ref 0 in
  let entry = entry_label func.name in
  let current_label = ref entry in
  let current_instrs = ref [] in
  let blocks = ref [] in
  let start_block label =
    current_label := label;
    current_instrs := []
  in
  let emit terminator =
    blocks :=
      {
        label = !current_label;
        instrs = List.rev !current_instrs;
        terminator;
      }
      :: !blocks;
    current_instrs := []
  in
  let has_open_instrs () = !current_instrs <> [] in
  let rec loop = function
    | [] ->
        if has_open_instrs () || !blocks = [] then emit Unreachable;
        {
          name = func.name;
          entry;
          blocks = List.rev !blocks;
        }
    | Ir.Label label :: rest ->
        if has_open_instrs () then emit (Jump label);
        start_block label;
        loop rest
    | Ir.Jump label :: rest ->
        emit (Jump label);
        start_block (fresh_label func.name "dead" counter);
        loop rest
    | Ir.Return operand :: rest ->
        emit (Return operand);
        start_block (fresh_label func.name "dead" counter);
        loop rest
    | Ir.BranchZero (operand, zero_label) :: rest -> (
        match rest with
        | Ir.Label nonzero_label :: _ ->
            emit (BranchZero (operand, zero_label, Some nonzero_label));
            start_block (fresh_label func.name "dead" counter);
            loop rest
        | [] ->
            emit (BranchZero (operand, zero_label, None));
            {
              name = func.name;
              entry;
              blocks = List.rev !blocks;
            }
        | _ ->
            let nonzero_label = fresh_label func.name "fallthrough" counter in
            emit (BranchZero (operand, zero_label, Some nonzero_label));
            start_block nonzero_label;
            loop rest)
    | instr :: rest ->
        if is_control instr then Diagnostic.fail "internal error: bad control split";
        current_instrs := instr :: !current_instrs;
        loop rest
  in
  loop func.body

let terminator_to_instrs = function
  | Return operand -> [ Ir.Return operand ]
  | Jump label -> [ Ir.Jump label ]
  | BranchZero (operand, zero_label, None) -> [ Ir.BranchZero (operand, zero_label) ]
  | BranchZero (operand, zero_label, Some nonzero_label) ->
      [ Ir.BranchZero (operand, zero_label); Ir.Jump nonzero_label ]
  | BranchCmp _ -> Diagnostic.fail "internal error: BranchCmp needs a temporary register"
  | Unreachable -> []

let to_ir_func func =
  let max_reg_operand current = function
    | Ir.Imm _ -> current
    | Ir.Reg reg -> max current reg
  in
  let max_reg_instr current = function
    | Ir.LoadParam (dest, _) -> max current dest
    | Ir.Move (dest, operand) | Ir.Unary (dest, _, operand)
    | Ir.ShiftLeft (dest, operand, _) ->
        max current dest |> fun current -> max_reg_operand current operand
    | Ir.Binary (dest, _, lhs, rhs) ->
        max current dest
        |> fun current -> max_reg_operand current lhs
        |> fun current -> max_reg_operand current rhs
    | Ir.LoadGlobal (dest, _) -> max current dest
    | Ir.StoreGlobal (_, operand) | Ir.BranchZero (operand, _)
    | Ir.Return operand ->
        max_reg_operand current operand
    | Ir.Call (dest, _, args) ->
        let current =
          match dest with
          | None -> current
          | Some reg -> max current reg
        in
        List.fold_left max_reg_operand current args
    | Ir.Label _ | Ir.Jump _ -> current
  in
  let max_reg_terminator current = function
    | Return operand | BranchZero (operand, _, _) ->
        max_reg_operand current operand
    | BranchCmp (_, lhs, rhs, _, _) ->
        max_reg_operand current lhs |> fun current -> max_reg_operand current rhs
    | Jump _ | Unreachable -> current
  in
  let next_reg =
    func.blocks
    |> List.fold_left
         (fun current block ->
           let current = List.fold_left max_reg_instr current block.instrs in
           max_reg_terminator current block.terminator)
         (-1)
    |> ( + ) 1
    |> ref
  in
  let fresh_reg () =
    let reg = !next_reg in
    incr next_reg;
    reg
  in
  let terminator_to_instrs = function
    | BranchCmp (op, lhs, rhs, zero_label, nonzero_label) ->
        let tmp = fresh_reg () in
        Ir.Binary (tmp, op, lhs, rhs)
        :: terminator_to_instrs
             (BranchZero (Ir.Reg tmp, zero_label, nonzero_label))
    | terminator -> terminator_to_instrs terminator
  in
  let instrs =
    func.blocks
    |> List.mapi (fun index block ->
           let label =
             if index = 0 && block.label = func.entry then [] else [ Ir.Label block.label ]
           in
           label @ block.instrs @ terminator_to_instrs block.terminator)
    |> List.concat
  in
  { Ir.name = func.name; body = instrs }

let comparison_binop = function
  | Ast.Lt | Ast.Gt | Ast.Le | Ast.Ge | Ast.Eq | Ast.Ne -> true
  | Ast.Add | Ast.Sub | Ast.Mul | Ast.Div | Ast.Mod | Ast.LAnd | Ast.LOr -> false

let split_last values =
  let rec loop prefix = function
    | [] -> None
    | [ value ] -> Some (List.rev prefix, value)
    | value :: rest -> loop (value :: prefix) rest
  in
  loop [] values

let fuse_branch_cmp func =
  let blocks =
    List.map
      (fun block ->
        match (split_last block.instrs, block.terminator) with
        | ( Some
              ( instrs,
                Ir.Binary (dest, op, lhs, rhs) ),
            BranchZero (Ir.Reg reg, zero_label, nonzero_label) )
          when dest = reg && comparison_binop op ->
            {
              block with
              instrs;
              terminator = BranchCmp (op, lhs, rhs, zero_label, nonzero_label);
            }
        | _ -> block)
      func.blocks
  in
  { func with blocks }
