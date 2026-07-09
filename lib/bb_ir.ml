module StringMap = Map.Make (String)
module StringSet = Set.Make (String)
module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)

type label = string

type target = {
  label : label;
  args : Ir.operand list;
}

type terminator =
  | Return of Ir.operand
  | Jump of target
  | BranchZero of Ir.operand * target * target option
  | BranchCmp of Ast.binop * Ir.operand * Ir.operand * target * target option
  | Unreachable

type block = {
  label : label;
  params : Ir.vreg list;
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

let target ?(args = []) label = { label; args }

let terminator_successors = function
  | Return _ | Unreachable -> []
  | Jump target -> [ target.label ]
  | BranchZero (_, zero_target, None) -> [ zero_target.label ]
  | BranchZero (_, zero_target, Some nonzero_target) ->
      [ zero_target.label; nonzero_target.label ]
  | BranchCmp (_, _, _, zero_target, None) -> [ zero_target.label ]
  | BranchCmp (_, _, _, zero_target, Some nonzero_target) ->
      [ zero_target.label; nonzero_target.label ]

let operand_uses = function
  | Ir.Imm _ -> []
  | Ir.Reg reg -> [ reg ]

let terminator_uses = function
  | Return operand -> operand_uses operand
  | Jump target -> List.concat_map operand_uses target.args
  | BranchZero (operand, zero_target, nonzero_target) ->
      operand_uses operand @ List.concat_map operand_uses zero_target.args
      @ (match nonzero_target with
        | None -> []
        | Some target -> List.concat_map operand_uses target.args)
  | BranchCmp (_, lhs, rhs, zero_target, nonzero_target) ->
      operand_uses lhs @ operand_uses rhs
      @ List.concat_map operand_uses zero_target.args
      @ (match nonzero_target with
        | None -> []
        | Some target -> List.concat_map operand_uses target.args)
  | Unreachable -> []

let is_control = function
  | Ir.Label _ | Ir.BranchZero _ | Ir.Jump _ | Ir.Return _ -> true
  | _ -> false

let block_map blocks =
  List.fold_left
    (fun blocks block -> StringMap.add block.label block blocks)
    StringMap.empty blocks

let block_index_map blocks =
  blocks
  |> List.mapi (fun index block -> (block.label, index))
  |> List.fold_left
       (fun blocks (label, index) -> StringMap.add label index blocks)
       StringMap.empty

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
        params = [];
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
        if has_open_instrs () then emit (Jump (target label));
        start_block label;
        loop rest
    | Ir.Jump label :: rest ->
        emit (Jump (target label));
        start_block (fresh_label func.name "dead" counter);
        loop rest
    | Ir.Return operand :: rest ->
        emit (Return operand);
        start_block (fresh_label func.name "dead" counter);
        loop rest
    | Ir.BranchZero (operand, zero_label) :: rest -> (
        match rest with
        | Ir.Label nonzero_label :: _ ->
            emit (BranchZero (operand, target zero_label, Some (target nonzero_label)));
            start_block (fresh_label func.name "dead" counter);
            loop rest
        | [] ->
            emit (BranchZero (operand, target zero_label, None));
            {
              name = func.name;
              entry;
              blocks = List.rev !blocks;
            }
        | _ ->
            let nonzero_label = fresh_label func.name "fallthrough" counter in
            emit (BranchZero (operand, target zero_label, Some (target nonzero_label)));
            start_block nonzero_label;
            loop rest)
    | instr :: rest ->
        if is_control instr then Diagnostic.fail "internal error: bad control split";
        current_instrs := instr :: !current_instrs;
        loop rest
  in
  loop func.body

let simple_terminator_to_instrs = function
  | Return operand -> [ Ir.Return operand ]
  | Jump target when target.args = [] -> [ Ir.Jump target.label ]
  | BranchZero (operand, zero_target, None) when zero_target.args = [] ->
      [ Ir.BranchZero (operand, zero_target.label) ]
  | BranchZero (operand, zero_target, Some nonzero_target)
    when zero_target.args = [] && nonzero_target.args = [] ->
      [ Ir.BranchZero (operand, zero_target.label); Ir.Jump nonzero_target.label ]
  | BranchCmp _ -> Diagnostic.fail "internal error: BranchCmp needs a temporary register"
  | Jump _ | BranchZero _ ->
      Diagnostic.fail "internal error: edge arguments need block lowering"
  | Unreachable -> []

let to_ir_func func =
  let blocks_by_label = block_map func.blocks in
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
  let max_reg_target current target =
    List.fold_left max_reg_operand current target.args
  in
  let max_reg_target_opt current = function
    | None -> current
    | Some target -> max_reg_target current target
  in
  let max_reg_terminator current = function
    | Return operand -> max_reg_operand current operand
    | BranchZero (operand, zero_target, nonzero_target) ->
        max_reg_operand current operand
        |> fun current -> max_reg_target current zero_target
        |> fun current -> max_reg_target_opt current nonzero_target
    | BranchCmp (_, lhs, rhs, zero_target, nonzero_target) ->
        max_reg_operand current lhs
        |> fun current -> max_reg_operand current rhs
        |> fun current -> max_reg_target current zero_target
        |> fun current -> max_reg_target_opt current nonzero_target
    | Jump target ->
        List.fold_left max_reg_operand current target.args
    | Unreachable -> current
  in
  let next_reg =
    func.blocks
    |> List.fold_left
         (fun current block ->
           let current = List.fold_left max current block.params in
           let current = List.fold_left max_reg_instr current block.instrs in
           max_reg_terminator current block.terminator)
         (-1)
    |> ( + ) 1
    |> ref
  in
  let next_edge = ref 0 in
  let fresh_reg () =
    let reg = !next_reg in
    incr next_reg;
    reg
  in
  let fresh_edge_label () = fresh_label func.name "edge" next_edge in
  let params_for (target : target) =
    match StringMap.find_opt target.label blocks_by_label with
    | Some block -> block.params
    | None -> Diagnostic.fail ("internal error: unknown block target: " ^ target.label)
  in
  let lower_target (target : target) =
    let params = params_for target in
    if List.length params <> List.length target.args then
      Diagnostic.fail ("internal error: block argument arity mismatch: " ^ target.label);
    if target.args = [] then [ Ir.Jump target.label ]
    else
      let temps = List.map (fun arg -> (fresh_reg (), arg)) target.args in
      let save_args = List.map (fun (tmp, arg) -> Ir.Move (tmp, arg)) temps in
      let load_params =
        List.map2
          (fun param (tmp, _) -> Ir.Move (param, Ir.Reg tmp))
          params temps
      in
      save_args @ load_params @ [ Ir.Jump target.label ]
  in
  let lower_edge (target : target) =
    let label = fresh_edge_label () in
    (label, Ir.Label label :: lower_target target)
  in
  let rec terminator_to_instrs = function
    | BranchCmp (op, lhs, rhs, zero_label, nonzero_label) ->
        let tmp = fresh_reg () in
        Ir.Binary (tmp, op, lhs, rhs)
        :: terminator_to_instrs
             (BranchZero (Ir.Reg tmp, zero_label, nonzero_label))
    | Jump target -> lower_target target
    | BranchZero (operand, zero_target, None) when zero_target.args = [] ->
        [ Ir.BranchZero (operand, zero_target.label) ]
    | BranchZero (operand, zero_target, None) ->
        let zero_label, zero_code = lower_edge zero_target in
        [ Ir.BranchZero (operand, zero_label) ] @ zero_code
    | BranchZero (operand, zero_target, Some nonzero_target)
      when zero_target.args = [] && nonzero_target.args = [] ->
        [ Ir.BranchZero (operand, zero_target.label); Ir.Jump nonzero_target.label ]
    | BranchZero (operand, zero_target, Some nonzero_target) ->
        let zero_label, zero_code = lower_edge zero_target in
        [ Ir.BranchZero (operand, zero_label) ]
        @ lower_target nonzero_target
        @ zero_code
    | terminator -> simple_terminator_to_instrs terminator
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

let operand_reg current = function
  | Ir.Imm _ -> current
  | Ir.Reg reg -> max current reg

let instr_max_reg current = function
  | Ir.LoadParam (dest, _) -> max current dest
  | Ir.Move (dest, operand) | Ir.Unary (dest, _, operand)
  | Ir.ShiftLeft (dest, operand, _) ->
      max current dest |> fun current -> operand_reg current operand
  | Ir.Binary (dest, _, lhs, rhs) ->
      max current dest
      |> fun current -> operand_reg current lhs
      |> fun current -> operand_reg current rhs
  | Ir.LoadGlobal (dest, _) -> max current dest
  | Ir.StoreGlobal (_, operand) | Ir.BranchZero (operand, _)
  | Ir.Return operand ->
      operand_reg current operand
  | Ir.Call (dest, _, args) ->
      let current =
        match dest with
        | None -> current
        | Some reg -> max current reg
      in
      List.fold_left operand_reg current args
  | Ir.Label _ | Ir.Jump _ -> current

let target_max_reg current target =
  List.fold_left operand_reg current target.args

let terminator_max_reg current = function
  | Return operand -> operand_reg current operand
  | Jump target -> target_max_reg current target
  | BranchZero (operand, zero_target, nonzero_target) ->
      operand_reg current operand
      |> fun current -> target_max_reg current zero_target
      |> fun current ->
      (match nonzero_target with
      | None -> current
      | Some target -> target_max_reg current target)
  | BranchCmp (_, lhs, rhs, zero_target, nonzero_target) ->
      operand_reg current lhs
      |> fun current -> operand_reg current rhs
      |> fun current -> target_max_reg current zero_target
      |> fun current ->
      (match nonzero_target with
      | None -> current
      | Some target -> target_max_reg current target)
  | Unreachable -> current

let max_reg_func func =
  List.fold_left
    (fun current block ->
      let current = List.fold_left max current block.params in
      let current = List.fold_left instr_max_reg current block.instrs in
      terminator_max_reg current block.terminator)
    (-1) func.blocks

let instr_uses = function
  | Ir.LoadParam _ | Ir.LoadGlobal _ | Ir.Label _ | Ir.Jump _ -> IntSet.empty
  | Ir.Move (_, operand) | Ir.Unary (_, _, operand)
  | Ir.ShiftLeft (_, operand, _) | Ir.StoreGlobal (_, operand)
  | Ir.BranchZero (operand, _) | Ir.Return operand ->
      operand_uses operand |> List.fold_left (fun uses reg -> IntSet.add reg uses) IntSet.empty
  | Ir.Binary (_, _, lhs, rhs) ->
      operand_uses lhs @ operand_uses rhs
      |> List.fold_left (fun uses reg -> IntSet.add reg uses) IntSet.empty
  | Ir.Call (_, _, args) ->
      args
      |> List.concat_map operand_uses
      |> List.fold_left (fun uses reg -> IntSet.add reg uses) IntSet.empty

let instr_dest = function
  | Ir.LoadParam (dest, _) | Ir.Move (dest, _) | Ir.Unary (dest, _, _)
  | Ir.Binary (dest, _, _, _) | Ir.ShiftLeft (dest, _, _)
  | Ir.LoadGlobal (dest, _) ->
      Some dest
  | Ir.Call (dest, _, _) -> dest
  | Ir.Label _ | Ir.StoreGlobal _ | Ir.BranchZero _ | Ir.Jump _ | Ir.Return _ ->
      None

let block_uses_defs block =
  let param_defs =
    List.fold_left (fun defs reg -> IntSet.add reg defs) IntSet.empty block.params
  in
  let uses, defs =
    List.fold_left
      (fun (uses, defs) instr ->
        let instr_uses = IntSet.diff (instr_uses instr) defs in
        let uses = IntSet.union uses instr_uses in
        let defs =
          match instr_dest instr with
          | None -> defs
          | Some dest -> IntSet.add dest defs
        in
        (uses, defs))
      (IntSet.empty, param_defs) block.instrs
  in
  let term_uses =
    terminator_uses block.terminator
    |> List.fold_left
         (fun uses reg -> if IntSet.mem reg defs then uses else IntSet.add reg uses)
         IntSet.empty
  in
  (IntSet.union uses term_uses, defs)

let compute_block_liveness func =
  let blocks = Array.of_list func.blocks in
  let count = Array.length blocks in
  let label_indices = block_index_map func.blocks in
  let succs =
    Array.map
      (fun block ->
        terminator_successors block.terminator
        |> List.filter_map (fun label -> StringMap.find_opt label label_indices))
      blocks
  in
  let uses, defs =
    Array.fold_right
      (fun block (uses, defs) ->
        let block_uses, block_defs = block_uses_defs block in
        (block_uses :: uses, block_defs :: defs))
      blocks ([], [])
  in
  let uses = Array.of_list uses in
  let defs = Array.of_list defs in
  let live_in = Array.make count IntSet.empty in
  let live_out = Array.make count IntSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for index = count - 1 downto 0 do
      let out_set =
        List.fold_left
          (fun acc succ -> IntSet.union acc live_in.(succ))
          IntSet.empty succs.(index)
      in
      let in_set =
        IntSet.union uses.(index)
          (IntSet.diff out_set defs.(index))
      in
      if not (IntSet.equal out_set live_out.(index)) then (
        live_out.(index) <- out_set;
        changed := true);
      if not (IntSet.equal in_set live_in.(index)) then (
        live_in.(index) <- in_set;
        changed := true)
    done
  done;
  (live_in, live_out)

let rewrite_operand env = function
  | Ir.Imm _ as imm -> imm
  | Ir.Reg reg -> (
      match IntMap.find_opt reg env with
      | None -> Ir.Reg reg
      | Some renamed -> Ir.Reg renamed)

let rewrite_target_arg env reg =
  match IntMap.find_opt reg env with
  | None -> Ir.Reg reg
  | Some renamed -> Ir.Reg renamed

let rewrite_instr env instr =
  let rewritten =
    match instr with
    | Ir.Move (dest, operand) -> Ir.Move (dest, rewrite_operand env operand)
    | Ir.Unary (dest, op, operand) ->
        Ir.Unary (dest, op, rewrite_operand env operand)
    | Ir.Binary (dest, op, lhs, rhs) ->
        Ir.Binary (dest, op, rewrite_operand env lhs, rewrite_operand env rhs)
    | Ir.ShiftLeft (dest, operand, amount) ->
        Ir.ShiftLeft (dest, rewrite_operand env operand, amount)
    | Ir.StoreGlobal (name, operand) ->
        Ir.StoreGlobal (name, rewrite_operand env operand)
    | Ir.Call (dest, name, args) ->
        Ir.Call (dest, name, List.map (rewrite_operand env) args)
    | Ir.LoadParam _ | Ir.LoadGlobal _ | Ir.Label _ | Ir.BranchZero _ | Ir.Jump _
    | Ir.Return _ ->
        instr
  in
  let env =
    match instr_dest instr with
    | None -> env
    | Some dest -> IntMap.remove dest env
  in
  (env, rewritten)

let add_livein_params func =
  let live_in, _ = compute_block_liveness func in
  let label_indices = block_index_map func.blocks in
  let next_reg = ref (max_reg_func func + 1) in
  let fresh () =
    let reg = !next_reg in
    incr next_reg;
    reg
  in
  let live_ins =
    Array.map (fun set -> IntSet.elements set) live_in
  in
  let param_maps =
    Array.mapi
      (fun index regs ->
        if index = 0 then IntMap.empty
        else
          List.fold_left
            (fun params reg -> IntMap.add reg (fresh ()) params)
            IntMap.empty regs)
      live_ins
  in
  let target_args env (target : target) =
    match StringMap.find_opt target.label label_indices with
    | None -> target.args
    | Some index ->
        live_ins.(index)
        |> List.map (rewrite_target_arg env)
  in
  let rewrite_target env (target : target) =
    { target with args = target_args env target }
  in
  let rewrite_terminator env = function
    | Return operand -> Return (rewrite_operand env operand)
    | Jump target -> Jump (rewrite_target env target)
    | BranchZero (operand, zero_target, nonzero_target) ->
        BranchZero
          ( rewrite_operand env operand,
            rewrite_target env zero_target,
            Option.map (rewrite_target env) nonzero_target )
    | BranchCmp (op, lhs, rhs, zero_target, nonzero_target) ->
        BranchCmp
          ( op,
            rewrite_operand env lhs,
            rewrite_operand env rhs,
            rewrite_target env zero_target,
            Option.map (rewrite_target env) nonzero_target )
    | Unreachable -> Unreachable
  in
  let blocks =
    func.blocks
    |> List.mapi (fun index block ->
           let param_map = param_maps.(index) in
           let params =
             live_ins.(index)
             |> List.filter_map (fun reg -> IntMap.find_opt reg param_map)
           in
           let env, instrs =
             List.fold_left
               (fun (env, instrs) instr ->
                 let env, instr = rewrite_instr env instr in
                 (env, instr :: instrs))
               (param_map, []) block.instrs
           in
           {
             block with
             params;
             instrs = List.rev instrs;
             terminator = rewrite_terminator env block.terminator;
           })
  in
  { func with blocks }
