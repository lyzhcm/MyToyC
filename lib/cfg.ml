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
