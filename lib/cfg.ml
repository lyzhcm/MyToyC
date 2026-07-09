module IntSet = Set.Make (Int)
module StringMap = Map.Make (String)

type block_id = int

type t = {
  instrs : Ir.instr array;
  succs : int list array;
  preds : int list array;
  uses : IntSet.t array;
  defs : IntSet.t array;
}

type block_t = {
  blocks : Bb_ir.block array;
  entry : block_id;
  block_succs : block_id list array;
  block_preds : block_id list array;
  block_uses : IntSet.t array;
  block_defs : IntSet.t array;
}

let operand_uses = function
  | Ir.Imm _ -> IntSet.empty
  | Ir.Reg reg -> IntSet.singleton reg

let instr_uses_defs = function
  | Ir.LoadParam (dest, _) -> (IntSet.empty, IntSet.singleton dest)
  | Ir.Move (dest, operand) -> (operand_uses operand, IntSet.singleton dest)
  | Ir.Unary (dest, _, operand) -> (operand_uses operand, IntSet.singleton dest)
  | Ir.Binary (dest, _, lhs, rhs) ->
      (IntSet.union (operand_uses lhs) (operand_uses rhs), IntSet.singleton dest)
  | Ir.ShiftLeft (dest, operand, _) ->
      (operand_uses operand, IntSet.singleton dest)
  | Ir.LoadGlobal (dest, _) -> (IntSet.empty, IntSet.singleton dest)
  | Ir.StoreGlobal (_, operand) -> (operand_uses operand, IntSet.empty)
  | Ir.Call (dest, _, args) ->
      ( List.fold_left
          (fun uses operand -> IntSet.union uses (operand_uses operand))
          IntSet.empty args,
        match dest with
        | None -> IntSet.empty
        | Some reg -> IntSet.singleton reg )
  | Ir.Label _ -> (IntSet.empty, IntSet.empty)
  | Ir.BranchZero (operand, _) -> (operand_uses operand, IntSet.empty)
  | Ir.Jump _ -> (IntSet.empty, IntSet.empty)
  | Ir.Return operand -> (operand_uses operand, IntSet.empty)

let build_label_map instrs =
  Array.fold_left
    (fun (index, labels) instr ->
      match instr with
      | Ir.Label label -> (index + 1, StringMap.add label index labels)
      | _ -> (index + 1, labels))
    (0, StringMap.empty) instrs
  |> snd

let next_index instrs index =
  if index + 1 < Array.length instrs then Some (index + 1) else None

let successors label_map instrs index instr =
  match instr with
  | Ir.Jump label -> [ StringMap.find label label_map ]
  | Ir.BranchZero (_, label) -> (
      match next_index instrs index with
      | Some next -> [ StringMap.find label label_map; next ]
      | None -> [ StringMap.find label label_map ])
  | Ir.Return _ -> []
  | _ -> (
      match next_index instrs index with
      | Some next -> [ next ]
      | None -> [])

let build_preds succs =
  let preds = Array.make (Array.length succs) [] in
  Array.iteri
    (fun index succ_list ->
      List.iter (fun succ -> preds.(succ) <- index :: preds.(succ)) succ_list)
    succs;
  preds

let build_block_label_map blocks =
  Array.fold_left
    (fun (index, labels) block ->
      (index + 1, StringMap.add block.Bb_ir.label index labels))
    (0, StringMap.empty) blocks
  |> snd

let lookup_label label_map label =
  match StringMap.find_opt label label_map with
  | Some index -> index
  | None -> Diagnostic.fail ("internal error: unknown block label: " ^ label)

let block_successors label_map block =
  block.Bb_ir.terminator
  |> Bb_ir.terminator_successors
  |> List.map (lookup_label label_map)

let add_instr_uses_defs (uses, defs) instr =
  let instr_uses, instr_defs = instr_uses_defs instr in
  (IntSet.union uses (IntSet.diff instr_uses defs), IntSet.union defs instr_defs)

let add_terminator_uses uses defs terminator =
  terminator
  |> Bb_ir.terminator_uses
  |> List.fold_left
       (fun uses reg ->
         if IntSet.mem reg defs then uses else IntSet.add reg uses)
       uses

let block_uses_defs block =
  let uses, defs =
    List.fold_left add_instr_uses_defs (IntSet.empty, IntSet.empty)
      block.Bb_ir.instrs
  in
  (add_terminator_uses uses defs block.Bb_ir.terminator, defs)

let of_instrs instrs =
  let instrs = Array.of_list instrs in
  let label_map = build_label_map instrs in
  let succs =
    Array.mapi (fun index instr -> successors label_map instrs index instr) instrs
  in
  let preds = build_preds succs in
  let uses, defs =
    Array.fold_right
      (fun instr (uses, defs) ->
        let uses_, defs_ = instr_uses_defs instr in
        (uses_ :: uses, defs_ :: defs))
      instrs ([], [])
  in
  { instrs; succs; preds; uses = Array.of_list uses; defs = Array.of_list defs }

let of_blocks func =
  let blocks = Array.of_list func.Bb_ir.blocks in
  let label_map = build_block_label_map blocks in
  let succs = Array.map (block_successors label_map) blocks in
  let preds = build_preds succs in
  let uses, defs =
    Array.fold_right
      (fun block (uses, defs) ->
        let uses_, defs_ = block_uses_defs block in
        (uses_ :: uses, defs_ :: defs))
      blocks ([], [])
  in
  {
    blocks;
    entry = lookup_label label_map func.Bb_ir.entry;
    block_succs = succs;
    block_preds = preds;
    block_uses = Array.of_list uses;
    block_defs = Array.of_list defs;
  }
