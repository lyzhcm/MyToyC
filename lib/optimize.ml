module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)
module StringSet = Set.Make (String)

type value =
  | Const of int
  | Copy of int

let i32 value =
  Int32.to_int (Int32.of_int value)

let apply_unop op value =
  match op with
  | Ast.Pos -> i32 value
  | Ast.Neg -> Int32.(to_int (neg (of_int value)))
  | Ast.LNot -> if value = 0 then 1 else 0

let apply_binop op lhs rhs =
  match op with
  | Ast.Add -> Some Int32.(to_int (add (of_int lhs) (of_int rhs)))
  | Ast.Sub -> Some Int32.(to_int (sub (of_int lhs) (of_int rhs)))
  | Ast.Mul -> Some Int32.(to_int (mul (of_int lhs) (of_int rhs)))
  | Ast.Div ->
      if rhs = 0 then None
      else Some Int32.(to_int (div (of_int lhs) (of_int rhs)))
  | Ast.Mod ->
      if rhs = 0 then None
      else Some Int32.(to_int (rem (of_int lhs) (of_int rhs)))
  | Ast.Lt -> Some (if lhs < rhs then 1 else 0)
  | Ast.Gt -> Some (if lhs > rhs then 1 else 0)
  | Ast.Le -> Some (if lhs <= rhs then 1 else 0)
  | Ast.Ge -> Some (if lhs >= rhs then 1 else 0)
  | Ast.Eq -> Some (if lhs = rhs then 1 else 0)
  | Ast.Ne -> Some (if lhs <> rhs then 1 else 0)
  | Ast.LAnd -> Some (if lhs <> 0 && rhs <> 0 then 1 else 0)
  | Ast.LOr -> Some (if lhs <> 0 || rhs <> 0 then 1 else 0)

let rec value_depends_on env seen target = function
  | Const _ -> false
  | Copy reg ->
      reg = target
      ||
      if IntSet.mem reg seen then false
      else
        match IntMap.find_opt reg env with
        | None -> false
        | Some value -> value_depends_on env (IntSet.add reg seen) target value

let kill_reg reg env =
  env
  |> IntMap.remove reg
  |> IntMap.filter (fun _ value -> not (value_depends_on env IntSet.empty reg value))

let define_value dest value env =
  IntMap.add dest value (kill_reg dest env)

let rec rewrite_reg env seen reg =
  if IntSet.mem reg seen then Ir.Reg reg
  else
    match IntMap.find_opt reg env with
    | Some (Const value) -> Ir.Imm value
    | Some (Copy source) -> (
        match rewrite_reg env (IntSet.add reg seen) source with
        | Ir.Imm _ as imm -> imm
        | Ir.Reg resolved -> Ir.Reg resolved)
    | None -> Ir.Reg reg

let rewrite_operand env = function
  | Ir.Imm _ as imm -> imm
  | Ir.Reg reg -> rewrite_reg env IntSet.empty reg

let clear_dest env = function
  | None -> env
  | Some reg -> kill_reg reg env

let same_operand lhs rhs =
  match (lhs, rhs) with
  | Ir.Imm lhs, Ir.Imm rhs -> lhs = rhs
  | Ir.Reg lhs, Ir.Reg rhs -> lhs = rhs
  | _ -> false

let is_power_of_two value =
  value > 0 && value land (value - 1) = 0

let log2 value =
  let rec loop shift value =
    if value = 1 then shift else loop (shift + 1) (value lsr 1)
  in
  loop 0 value

let move_or_nop dest operand =
  match operand with
  | Ir.Reg reg when reg = dest -> []
  | _ -> [ Ir.Move (dest, operand) ]

let unary_instr dest op operand =
  match operand with
  | Ir.Imm value -> [ Ir.Move (dest, Ir.Imm (apply_unop op value)) ]
  | Ir.Reg _ -> [ Ir.Unary (dest, op, operand) ]

let simplified_binary dest op lhs rhs =
  match (lhs, rhs) with
  | Ir.Imm lhs_value, Ir.Imm rhs_value -> (
      match apply_binop op lhs_value rhs_value with
      | Some value -> [ Ir.Move (dest, Ir.Imm value) ]
      | None -> [ Ir.Binary (dest, op, lhs, rhs) ])
  | _ -> (
      match (op, lhs, rhs) with
      | Ast.Add, operand, Ir.Imm 0 | Ast.Add, Ir.Imm 0, operand ->
          move_or_nop dest operand
      | Ast.Sub, operand, Ir.Imm 0 -> move_or_nop dest operand
      | Ast.Sub, Ir.Imm 0, operand -> unary_instr dest Ast.Neg operand
      | Ast.Mul, _, Ir.Imm 0 | Ast.Mul, Ir.Imm 0, _ ->
          [ Ir.Move (dest, Ir.Imm 0) ]
      | Ast.Mul, operand, Ir.Imm 1 | Ast.Mul, Ir.Imm 1, operand ->
          move_or_nop dest operand
      | Ast.Mul, operand, Ir.Imm (-1) | Ast.Mul, Ir.Imm (-1), operand ->
          unary_instr dest Ast.Neg operand
      | Ast.Mul, operand, Ir.Imm value
        when is_power_of_two value && log2 value < 32 ->
          [ Ir.ShiftLeft (dest, operand, log2 value) ]
      | Ast.Mul, Ir.Imm value, operand
        when is_power_of_two value && log2 value < 32 ->
          [ Ir.ShiftLeft (dest, operand, log2 value) ]
      | Ast.Div, operand, Ir.Imm 1 -> move_or_nop dest operand
      | Ast.Div, operand, Ir.Imm (-1) -> unary_instr dest Ast.Neg operand
      | Ast.Div, Ir.Imm 0, _ -> [ Ir.Move (dest, Ir.Imm 0) ]
      | Ast.Mod, _, Ir.Imm 1 | Ast.Mod, _, Ir.Imm (-1) | Ast.Mod, Ir.Imm 0, _
        ->
          [ Ir.Move (dest, Ir.Imm 0) ]
      | (Ast.Eq | Ast.Le | Ast.Ge), _, _ when same_operand lhs rhs ->
          [ Ir.Move (dest, Ir.Imm 1) ]
      | (Ast.Ne | Ast.Lt | Ast.Gt), _, _ when same_operand lhs rhs ->
          [ Ir.Move (dest, Ir.Imm 0) ]
      | Ast.LAnd, _, Ir.Imm 0 | Ast.LAnd, Ir.Imm 0, _ ->
          [ Ir.Move (dest, Ir.Imm 0) ]
      | Ast.LOr, _, Ir.Imm value when value <> 0 ->
          [ Ir.Move (dest, Ir.Imm 1) ]
      | Ast.LOr, Ir.Imm value, _ when value <> 0 ->
          [ Ir.Move (dest, Ir.Imm 1) ]
      | _ -> [ Ir.Binary (dest, op, lhs, rhs) ])

let value_from_instr dest = function
  | [ Ir.Move (_, Ir.Imm value) ] -> Some (Const value)
  | [ Ir.Move (_, Ir.Reg reg) ] when reg <> dest -> Some (Copy reg)
  | [] -> None
  | _ -> None

let add_rewritten instrs acc =
  List.rev_append instrs acc

let optimize_instrs body =
  let rec loop env reachable acc = function
    | [] -> List.rev acc
    | Ir.Label label :: rest ->
        loop IntMap.empty true (Ir.Label label :: acc) rest
    | _ :: rest when not reachable -> loop env false acc rest
    | instr :: rest -> (
        match instr with
        | Ir.LoadParam (dest, index) ->
            loop (kill_reg dest env) true
              (Ir.LoadParam (dest, index) :: acc)
              rest
        | Ir.Move (dest, operand) ->
            let operand = rewrite_operand env operand in
            let instrs = move_or_nop dest operand in
            let env =
              match operand with
              | Ir.Reg reg when reg = dest -> env
              | Ir.Imm value -> define_value dest (Const value) env
              | Ir.Reg reg -> define_value dest (Copy reg) env
            in
            loop env true (add_rewritten instrs acc) rest
        | Ir.Unary (dest, op, operand) ->
            let operand = rewrite_operand env operand in
            let instrs = unary_instr dest op operand in
            let env =
              match value_from_instr dest instrs with
              | Some value -> define_value dest value env
              | None -> kill_reg dest env
            in
            loop env true (add_rewritten instrs acc) rest
        | Ir.Binary (dest, op, lhs, rhs) ->
            let lhs = rewrite_operand env lhs in
            let rhs = rewrite_operand env rhs in
            let instrs = simplified_binary dest op lhs rhs in
            let env =
              match value_from_instr dest instrs with
              | Some value -> define_value dest value env
              | None -> kill_reg dest env
            in
            loop env true (add_rewritten instrs acc) rest
        | Ir.ShiftLeft (dest, operand, amount) ->
            let operand = rewrite_operand env operand in
            let instrs =
              match operand with
              | Ir.Imm value ->
                  [ Ir.Move
                      ( dest,
                        Ir.Imm
                          Int32.(
                            to_int
                              (shift_left (of_int value) amount)) ) ]
              | Ir.Reg _ when amount = 0 -> move_or_nop dest operand
              | Ir.Reg _ -> [ Ir.ShiftLeft (dest, operand, amount) ]
            in
            let env =
              match value_from_instr dest instrs with
              | Some value -> define_value dest value env
              | None -> kill_reg dest env
            in
            loop env true (add_rewritten instrs acc) rest
        | Ir.LoadGlobal (dest, name) ->
            loop (kill_reg dest env) true
              (Ir.LoadGlobal (dest, name) :: acc)
              rest
        | Ir.Label label ->
            loop IntMap.empty true (Ir.Label label :: acc) rest
        | Ir.StoreGlobal (name, operand) ->
            let operand = rewrite_operand env operand in
            loop env true (Ir.StoreGlobal (name, operand) :: acc) rest
        | Ir.Call (dest, name, args) ->
            let args = List.map (rewrite_operand env) args in
            let env = clear_dest env dest in
            loop env true (Ir.Call (dest, name, args) :: acc) rest
        | Ir.BranchZero (operand, label) ->
            let operand = rewrite_operand env operand in
            let acc, env, reachable =
              match operand with
              | Ir.Imm 0 -> (Ir.Jump label :: acc, IntMap.empty, false)
              | Ir.Imm _ -> (acc, env, true)
              | _ -> (Ir.BranchZero (operand, label) :: acc, IntMap.empty, true)
            in
            loop env reachable acc rest
        | Ir.Jump label ->
            loop IntMap.empty false (Ir.Jump label :: acc) rest
        | Ir.Return operand ->
            let operand = rewrite_operand env operand in
            loop IntMap.empty false (Ir.Return operand :: acc) rest)
  in
  body |> loop IntMap.empty true []

let remove_redundant_jumps body =
  let rec remove_redundant_jumps acc = function
    | Ir.Jump target :: Ir.Label label :: rest when target = label ->
        remove_redundant_jumps (Ir.Label label :: acc) rest
    | instr :: rest -> remove_redundant_jumps (instr :: acc) rest
    | [] -> List.rev acc
  in
  remove_redundant_jumps [] body

let reachable_indices body =
  let cfg = Cfg.of_instrs body in
  let count = Array.length cfg.Cfg.instrs in
  let seen = Array.make count false in
  let rec visit = function
    | [] -> ()
    | index :: rest ->
        if index < 0 || index >= count || seen.(index) then visit rest
        else (
          seen.(index) <- true;
          visit (cfg.Cfg.succs.(index) @ rest))
  in
  if count > 0 then visit [ 0 ];
  seen

let remove_unreachable_instrs body =
  let reachable = reachable_indices body in
  body
  |> List.mapi (fun index instr -> (index, instr))
  |> List.filter_map (fun (index, instr) ->
         if reachable.(index) then Some instr else None)

let referenced_labels body =
  List.fold_left
    (fun labels instr ->
      match instr with
      | Ir.BranchZero (_, label) | Ir.Jump label -> StringSet.add label labels
      | _ -> labels)
    StringSet.empty body

let remove_unused_labels body =
  let labels = referenced_labels body in
  List.filter
    (function
      | Ir.Label label -> StringSet.mem label labels
      | _ -> true)
    body

let removable_dead_def instr live_out =
  let dead reg = not (Liveness.IntSet.mem reg live_out) in
  match instr with
  | Ir.LoadParam (dest, _) when dead dest -> true
  | Ir.Move (dest, _) when dead dest -> true
  | Ir.Unary (dest, _, _) when dead dest -> true
  | Ir.Binary (dest, _, _, _) when dead dest -> true
  | Ir.ShiftLeft (dest, _, _) when dead dest -> true
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

let cleanup_control_flow body =
  body
  |> remove_redundant_jumps
  |> remove_unreachable_instrs
  |> remove_redundant_jumps
  |> remove_unused_labels

let optimize_body body =
  let rec fix body =
    let next =
      body
      |> optimize_instrs
      |> cleanup_control_flow
      |> eliminate_dead_defs
      |> cleanup_control_flow
    in
    if next = body then body else fix next
  in
  fix body

let optimize_func func =
  { func with Ir.body = optimize_body func.Ir.body }

let run ~enabled (program : Ir.program) =
  if not enabled then program
  else { program with Ir.funcs = List.map optimize_func program.Ir.funcs }
