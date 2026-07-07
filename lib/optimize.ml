module IntMap = Map.Make (Int)

let apply_unop op value =
  match op with
  | Ast.Pos -> value
  | Ast.Neg -> -value
  | Ast.LNot -> if value = 0 then 1 else 0

let apply_binop op lhs rhs =
  match op with
  | Ast.Add -> Some (lhs + rhs)
  | Ast.Sub -> Some (lhs - rhs)
  | Ast.Mul -> Some (lhs * rhs)
  | Ast.Div -> if rhs = 0 then None else Some (lhs / rhs)
  | Ast.Mod -> if rhs = 0 then None else Some (lhs mod rhs)
  | Ast.Lt -> Some (if lhs < rhs then 1 else 0)
  | Ast.Gt -> Some (if lhs > rhs then 1 else 0)
  | Ast.Le -> Some (if lhs <= rhs then 1 else 0)
  | Ast.Ge -> Some (if lhs >= rhs then 1 else 0)
  | Ast.Eq -> Some (if lhs = rhs then 1 else 0)
  | Ast.Ne -> Some (if lhs <> rhs then 1 else 0)
  | Ast.LAnd -> Some (if lhs <> 0 && rhs <> 0 then 1 else 0)
  | Ast.LOr -> Some (if lhs <> 0 || rhs <> 0 then 1 else 0)

let rewrite_operand consts = function
  | Ir.Imm _ as imm -> imm
  | Ir.Reg reg -> (
      match IntMap.find_opt reg consts with
      | Some value -> Ir.Imm value
      | None -> Ir.Reg reg)

let clear_dest consts = function
  | None -> consts
  | Some reg -> IntMap.remove reg consts

let optimize_instrs body =
  let rec loop consts reachable acc = function
    | [] -> List.rev acc
    | Ir.Label label :: rest ->
        loop IntMap.empty true (Ir.Label label :: acc) rest
    | _ :: rest when not reachable -> loop consts false acc rest
    | instr :: rest -> (
        match instr with
        | Ir.LoadParam (dest, index) ->
            loop (IntMap.remove dest consts) true
              (Ir.LoadParam (dest, index) :: acc)
              rest
        | Ir.Move (dest, operand) ->
            let operand = rewrite_operand consts operand in
            let consts =
              match operand with
              | Ir.Imm value -> IntMap.add dest value consts
              | Ir.Reg _ -> IntMap.remove dest consts
            in
            loop consts true (Ir.Move (dest, operand) :: acc) rest
        | Ir.Unary (dest, op, operand) ->
            let operand = rewrite_operand consts operand in
            let instr, consts =
              match operand with
              | Ir.Imm value ->
                  let value = apply_unop op value in
                  (Ir.Move (dest, Ir.Imm value), IntMap.add dest value consts)
              | Ir.Reg _ ->
                  (Ir.Unary (dest, op, operand), IntMap.remove dest consts)
            in
            loop consts true (instr :: acc) rest
        | Ir.Binary (dest, op, lhs, rhs) ->
            let lhs = rewrite_operand consts lhs in
            let rhs = rewrite_operand consts rhs in
            let instr, consts =
              match (lhs, rhs) with
              | Ir.Imm lhs_value, Ir.Imm rhs_value -> (
                  match apply_binop op lhs_value rhs_value with
                  | Some value ->
                      (Ir.Move (dest, Ir.Imm value), IntMap.add dest value consts)
                  | None ->
                      (Ir.Binary (dest, op, lhs, rhs), IntMap.remove dest consts))
              | _ -> (Ir.Binary (dest, op, lhs, rhs), IntMap.remove dest consts)
            in
            loop consts true (instr :: acc) rest
        | Ir.LoadGlobal (dest, name) ->
            loop (IntMap.remove dest consts) true
              (Ir.LoadGlobal (dest, name) :: acc)
              rest
        | Ir.Label label ->
            loop IntMap.empty true (Ir.Label label :: acc) rest
        | Ir.StoreGlobal (name, operand) ->
            let operand = rewrite_operand consts operand in
            loop consts true (Ir.StoreGlobal (name, operand) :: acc) rest
        | Ir.Call (dest, name, args) ->
            let args = List.map (rewrite_operand consts) args in
            let consts = clear_dest consts dest in
            loop consts true (Ir.Call (dest, name, args) :: acc) rest
        | Ir.BranchZero (operand, label) ->
            let operand = rewrite_operand consts operand in
            let acc, reachable =
              match operand with
              | Ir.Imm 0 -> (Ir.Jump label :: acc, false)
              | Ir.Imm _ -> (acc, true)
              | _ -> (Ir.BranchZero (operand, label) :: acc, true)
            in
            loop IntMap.empty reachable acc rest
        | Ir.Jump label ->
            loop IntMap.empty false (Ir.Jump label :: acc) rest
        | Ir.Return operand ->
            let operand = rewrite_operand consts operand in
            loop IntMap.empty false (Ir.Return operand :: acc) rest)
  in
  let rec remove_redundant_jumps acc = function
    | Ir.Jump target :: Ir.Label label :: rest when target = label ->
        remove_redundant_jumps (Ir.Label label :: acc) rest
    | instr :: rest -> remove_redundant_jumps (instr :: acc) rest
    | [] -> List.rev acc
  in
  body |> loop IntMap.empty true [] |> remove_redundant_jumps []

let removable_dead_def instr live_out =
  let dead reg = not (Liveness.IntSet.mem reg live_out) in
  match instr with
  | Ir.LoadParam (dest, _) when dead dest -> true
  | Ir.Move (dest, _) when dead dest -> true
  | Ir.Unary (dest, _, _) when dead dest -> true
  | Ir.Binary (dest, _, _, _) when dead dest -> true
  | Ir.LoadGlobal (dest, _) when dead dest -> true
  | _ -> false

let eliminate_dead_defs body =
  let rec fix body =
    let cfg = Cfg.of_instrs body in
    let liveness = Liveness.analyze cfg in
    let filtered =
      cfg.instrs
      |> Array.to_list
      |> List.mapi (fun index instr -> (index, instr))
      |> List.filter_map (fun (index, instr) ->
             if removable_dead_def instr liveness.live_out.(index) then None
             else Some instr)
    in
    if List.length filtered = List.length body then body else fix filtered
  in
  fix body

let optimize_func func =
  { func with Ir.body = func.Ir.body |> optimize_instrs |> eliminate_dead_defs }

let run ~enabled (program : Ir.program) =
  if not enabled then program
  else { program with Ir.funcs = List.map optimize_func program.Ir.funcs }
