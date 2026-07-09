module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

type value =
  | Const of int
  | Copy of int

type expr_key =
  | EUnary of Ast.unop * Ir.operand
  | EBinary of Ast.binop * Ir.operand * Ir.operand
  | EShiftLeft of Ir.operand * int

module ExprMap = Map.Make (struct
  type t = expr_key

  let compare = compare
end)

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

let commutative_binop = function
  | Ast.Add | Ast.Mul | Ast.Eq | Ast.Ne | Ast.LAnd | Ast.LOr -> true
  | Ast.Sub | Ast.Div | Ast.Mod | Ast.Lt | Ast.Gt | Ast.Le | Ast.Ge -> false

let canonical_binop op lhs rhs =
  if commutative_binop op && compare rhs lhs < 0 then (rhs, lhs) else (lhs, rhs)

let operand_regs = function
  | Ir.Imm _ -> IntSet.empty
  | Ir.Reg reg -> IntSet.singleton reg

let expr_regs = function
  | EUnary (_, operand) | EShiftLeft (operand, _) -> operand_regs operand
  | EBinary (_, lhs, rhs) -> IntSet.union (operand_regs lhs) (operand_regs rhs)

let expr_depends_on reg expr =
  IntSet.mem reg (expr_regs expr)

let kill_exprs reg exprs =
  ExprMap.filter
    (fun expr source -> source <> reg && not (expr_depends_on reg expr))
    exprs

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

let expr_of_instr = function
  | Ir.Unary (_, op, operand) -> Some (EUnary (op, operand))
  | Ir.Binary (_, op, lhs, rhs) ->
      let lhs, rhs = canonical_binop op lhs rhs in
      Some (EBinary (op, lhs, rhs))
  | Ir.ShiftLeft (_, operand, amount) -> Some (EShiftLeft (operand, amount))
  | _ -> None

let expr_of_instrs = function
  | [ instr ] -> expr_of_instr instr
  | _ -> None

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
      | Ast.Add, lhs, rhs when same_operand lhs rhs ->
          [ Ir.ShiftLeft (dest, lhs, 1) ]
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

let apply_cse dest instrs exprs =
  match expr_of_instrs instrs with
  | None -> instrs
  | Some expr -> (
      match ExprMap.find_opt expr exprs with
      | Some source -> move_or_nop dest (Ir.Reg source)
      | None -> instrs)

let remember_expr dest instrs exprs =
  let exprs = kill_exprs dest exprs in
  match expr_of_instrs instrs with
  | Some expr when not (expr_depends_on dest expr) -> ExprMap.add expr dest exprs
  | _ -> exprs

let add_rewritten instrs acc =
  List.rev_append instrs acc

let optimize_instrs body =
  let rec loop env exprs reachable acc = function
    | [] -> List.rev acc
    | Ir.Label label :: rest ->
        loop IntMap.empty ExprMap.empty true (Ir.Label label :: acc) rest
    | _ :: rest when not reachable -> loop env exprs false acc rest
    | instr :: rest -> (
        match instr with
        | Ir.LoadParam (dest, index) ->
            loop (kill_reg dest env) (kill_exprs dest exprs) true
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
            let exprs = kill_exprs dest exprs in
            loop env exprs true (add_rewritten instrs acc) rest
        | Ir.Unary (dest, op, operand) ->
            let operand = rewrite_operand env operand in
            let instrs = unary_instr dest op operand |> fun instrs -> apply_cse dest instrs exprs in
            let env =
              match value_from_instr dest instrs with
              | Some value -> define_value dest value env
              | None -> kill_reg dest env
            in
            let exprs = remember_expr dest instrs exprs in
            loop env exprs true (add_rewritten instrs acc) rest
        | Ir.Binary (dest, op, lhs, rhs) ->
            let lhs = rewrite_operand env lhs in
            let rhs = rewrite_operand env rhs in
            let instrs = simplified_binary dest op lhs rhs |> fun instrs -> apply_cse dest instrs exprs in
            let env =
              match value_from_instr dest instrs with
              | Some value -> define_value dest value env
              | None -> kill_reg dest env
            in
            let exprs = remember_expr dest instrs exprs in
            loop env exprs true (add_rewritten instrs acc) rest
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
            let instrs = apply_cse dest instrs exprs in
            let env =
              match value_from_instr dest instrs with
              | Some value -> define_value dest value env
              | None -> kill_reg dest env
            in
            let exprs = remember_expr dest instrs exprs in
            loop env exprs true (add_rewritten instrs acc) rest
        | Ir.LoadGlobal (dest, name) ->
            loop (kill_reg dest env) (kill_exprs dest exprs) true
              (Ir.LoadGlobal (dest, name) :: acc)
              rest
        | Ir.Label label ->
            loop IntMap.empty ExprMap.empty true (Ir.Label label :: acc) rest
        | Ir.StoreGlobal (name, operand) ->
            let operand = rewrite_operand env operand in
            loop env exprs true (Ir.StoreGlobal (name, operand) :: acc) rest
        | Ir.Call (dest, name, args) ->
            let args = List.map (rewrite_operand env) args in
            let env = clear_dest env dest in
            let exprs =
              match dest with
              | None -> exprs
              | Some reg -> kill_exprs reg exprs
            in
            loop env exprs true (Ir.Call (dest, name, args) :: acc) rest
        | Ir.BranchZero (operand, label) ->
            let operand = rewrite_operand env operand in
            let acc, env, exprs, reachable =
              match operand with
              | Ir.Imm 0 -> (Ir.Jump label :: acc, IntMap.empty, ExprMap.empty, false)
              | Ir.Imm _ -> (acc, env, exprs, true)
              | _ ->
                  ( Ir.BranchZero (operand, label) :: acc,
                    IntMap.empty,
                    ExprMap.empty,
                    true )
            in
            loop env exprs reachable acc rest
        | Ir.Jump label ->
            loop IntMap.empty ExprMap.empty false (Ir.Jump label :: acc) rest
        | Ir.Return operand ->
            let operand = rewrite_operand env operand in
            loop IntMap.empty ExprMap.empty false (Ir.Return operand :: acc) rest)
  in
  body |> loop IntMap.empty ExprMap.empty true []

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

let resets_dead_store_block = function
  | Ir.Label _ | Ir.BranchZero _ | Ir.Jump _ | Ir.Return _ | Ir.Call _ -> true
  | _ -> false

let eliminate_dead_stores body =
  let optimize_block block =
    let _, kept =
      block
      |> List.rev
      |> List.fold_left
        (fun (overwritten, kept) instr ->
          match instr with
          | Ir.StoreGlobal (name, _) ->
              if StringSet.mem name overwritten then (overwritten, kept)
              else (StringSet.add name overwritten, instr :: kept)
          | Ir.LoadGlobal (_, name) ->
              (StringSet.remove name overwritten, instr :: kept)
          | _ -> (overwritten, instr :: kept))
        (StringSet.empty, [])
    in
    kept
  in
  let flush acc_rev block_rev boundary =
    let optimized = block_rev |> List.rev |> optimize_block in
    match boundary with
    | None -> List.rev (List.rev_append optimized acc_rev)
    | Some instr -> instr :: List.rev_append optimized acc_rev
  in
  let rec loop acc_rev block_rev = function
    | [] -> flush acc_rev block_rev None
    | instr :: rest when resets_dead_store_block instr ->
        loop (flush acc_rev block_rev (Some instr)) [] rest
    | instr :: rest -> loop acc_rev (instr :: block_rev) rest
  in
  loop [] [] body

type lattice =
  | LUnknown
  | LConst of int
  | LOverdef

let lattice_equal lhs rhs =
  match (lhs, rhs) with
  | LUnknown, LUnknown | LOverdef, LOverdef -> true
  | LConst lhs, LConst rhs -> lhs = rhs
  | _ -> false

let merge_lattice lhs rhs =
  match (lhs, rhs) with
  | LUnknown, value | value, LUnknown -> value
  | LConst lhs, LConst rhs when lhs = rhs -> LConst lhs
  | _ -> LOverdef

let get_lattice reg env =
  IntMap.find_opt reg env |> Option.value ~default:LUnknown

let set_lattice reg value env =
  IntMap.add reg value env

let merge_env lhs rhs =
  IntMap.merge
    (fun _ lhs rhs ->
      match (lhs, rhs) with
      | None, None -> None
      | Some value, None | None, Some value -> Some value
      | Some lhs, Some rhs -> Some (merge_lattice lhs rhs))
    lhs rhs

let env_equal lhs rhs =
  IntMap.equal lattice_equal lhs rhs

let const_operand env = function
  | Ir.Imm value -> LConst value
  | Ir.Reg reg -> get_lattice reg env

let rewrite_const_operand env = function
  | Ir.Imm _ as imm -> imm
  | Ir.Reg reg -> (
      match get_lattice reg env with
      | LConst value -> Ir.Imm value
      | LUnknown | LOverdef -> Ir.Reg reg)

let const_unop op operand =
  match operand with
  | LConst value -> LConst (apply_unop op value)
  | LUnknown -> LUnknown
  | LOverdef -> LOverdef

let const_binop op lhs rhs =
  match (lhs, rhs) with
  | LConst lhs, LConst rhs -> (
      match apply_binop op lhs rhs with
      | Some value -> LConst value
      | None -> LOverdef)
  | LOverdef, _ | _, LOverdef -> LOverdef
  | LUnknown, _ | _, LUnknown -> LUnknown

let define_const dest value env =
  set_lattice dest value env

let transfer_const env instr =
  match instr with
  | Ir.LoadParam (dest, _) | Ir.LoadGlobal (dest, _) ->
      define_const dest LOverdef env
  | Ir.Move (dest, operand) ->
      define_const dest (const_operand env operand) env
  | Ir.Unary (dest, op, operand) ->
      define_const dest (const_unop op (const_operand env operand)) env
  | Ir.Binary (dest, op, lhs, rhs) ->
      define_const dest
        (const_binop op (const_operand env lhs) (const_operand env rhs))
        env
  | Ir.ShiftLeft (dest, operand, amount) -> (
      match const_operand env operand with
      | LConst value ->
          define_const dest
            (LConst Int32.(to_int (shift_left (of_int value) amount)))
            env
      | LUnknown -> define_const dest LUnknown env
      | LOverdef -> define_const dest LOverdef env)
  | Ir.Call (dest, _, _) -> (
      match dest with
      | None -> env
      | Some dest -> define_const dest LOverdef env)
  | Ir.Label _ | Ir.StoreGlobal _ | Ir.BranchZero _ | Ir.Jump _ | Ir.Return _ ->
      env

let effective_succs env cfg index =
  match cfg.Cfg.instrs.(index) with
  | Ir.BranchZero (operand, _) -> (
      match rewrite_const_operand env operand with
      | Ir.Imm 0 -> [ List.hd cfg.Cfg.succs.(index) ]
      | Ir.Imm _ -> (
          match cfg.Cfg.succs.(index) with
          | _target :: fallthrough :: _ -> [ fallthrough ]
          | [] | [ _ ] -> [])
      | Ir.Reg _ -> cfg.Cfg.succs.(index))
  | _ -> cfg.Cfg.succs.(index)

let constant_dataflow body =
  let cfg = Cfg.of_instrs body in
  let count = Array.length cfg.Cfg.instrs in
  let in_envs = Array.make count IntMap.empty in
  let out_envs = Array.make count IntMap.empty in
  let reachable = Array.make count false in
  let changed = ref true in
  if count > 0 then reachable.(0) <- true;
  while !changed do
    changed := false;
    for index = 0 to count - 1 do
      if reachable.(index) then (
        let in_env =
          List.fold_left
            (fun env pred ->
              if reachable.(pred) then merge_env env out_envs.(pred) else env)
            IntMap.empty cfg.Cfg.preds.(index)
        in
        if not (env_equal in_env in_envs.(index)) then (
          in_envs.(index) <- in_env;
          changed := true);
        let out_env = transfer_const in_env cfg.Cfg.instrs.(index) in
        if not (env_equal out_env out_envs.(index)) then (
          out_envs.(index) <- out_env;
          changed := true);
        List.iter
          (fun succ ->
            if not reachable.(succ) then (
              reachable.(succ) <- true;
              changed := true))
          (effective_succs out_env cfg index))
    done
  done;
  (cfg, in_envs, out_envs, reachable)

let rewrite_with_constants body =
  let cfg, in_envs, out_envs, reachable = constant_dataflow body in
  let label_map =
    Array.fold_left
      (fun (index, labels) instr ->
        match instr with
        | Ir.Label label -> (index + 1, StringMap.add label index labels)
        | _ -> (index + 1, labels))
      (0, StringMap.empty) cfg.Cfg.instrs
    |> snd
  in
  cfg.Cfg.instrs
  |> Array.to_list
  |> List.mapi (fun index instr -> (index, instr))
  |> List.filter_map (fun (index, instr) ->
         if not reachable.(index) then None
         else
           let env = in_envs.(index) in
           let out_env = out_envs.(index) in
           match instr with
           | Ir.Move (dest, operand) ->
               Some (Ir.Move (dest, rewrite_const_operand env operand))
           | Ir.Unary (dest, op, operand) -> (
               let operand = rewrite_const_operand env operand in
               match const_unop op (const_operand env operand) with
               | LConst value -> Some (Ir.Move (dest, Ir.Imm value))
               | LUnknown | LOverdef -> Some (Ir.Unary (dest, op, operand)))
           | Ir.Binary (dest, op, lhs, rhs) -> (
               let lhs = rewrite_const_operand env lhs in
               let rhs = rewrite_const_operand env rhs in
               match const_binop op (const_operand env lhs) (const_operand env rhs) with
               | LConst value -> Some (Ir.Move (dest, Ir.Imm value))
               | LUnknown | LOverdef -> Some (Ir.Binary (dest, op, lhs, rhs)))
           | Ir.ShiftLeft (dest, operand, amount) -> (
               let operand = rewrite_const_operand env operand in
               match operand with
               | Ir.Imm value ->
                   Some
                     (Ir.Move
                        ( dest,
                          Ir.Imm Int32.(to_int (shift_left (of_int value) amount)) ))
               | Ir.Reg _ -> Some (Ir.ShiftLeft (dest, operand, amount)))
           | Ir.StoreGlobal (name, operand) ->
               Some (Ir.StoreGlobal (name, rewrite_const_operand env operand))
           | Ir.Call (dest, name, args) ->
               Some (Ir.Call (dest, name, List.map (rewrite_const_operand env) args))
           | Ir.BranchZero (operand, label) -> (
               match rewrite_const_operand env operand with
               | Ir.Imm 0 -> Some (Ir.Jump label)
               | Ir.Imm _ -> None
               | operand -> Some (Ir.BranchZero (operand, label)))
           | Ir.Return operand ->
               Some (Ir.Return (rewrite_const_operand env operand))
           | Ir.Jump label -> (
               match StringMap.find_opt label label_map with
               | Some target when not reachable.(target) -> None
               | _ -> Some instr)
           | Ir.LoadParam (dest, index) -> (
               match get_lattice dest out_env with
               | LConst value -> Some (Ir.Move (dest, Ir.Imm value))
               | LUnknown | LOverdef -> Some (Ir.LoadParam (dest, index)))
           | Ir.LoadGlobal _ | Ir.Label _ -> Some instr)

let intersect_exprs lhs rhs =
  ExprMap.merge
    (fun _ lhs rhs ->
      match (lhs, rhs) with
      | Some lhs, Some rhs when lhs = rhs -> Some lhs
      | _ -> None)
    lhs rhs

let exprs_equal lhs rhs =
  ExprMap.equal Int.equal lhs rhs

let instr_dest = function
  | Ir.LoadParam (dest, _) | Ir.Move (dest, _) | Ir.Unary (dest, _, _)
  | Ir.Binary (dest, _, _, _) | Ir.ShiftLeft (dest, _, _)
  | Ir.LoadGlobal (dest, _) ->
      Some dest
  | Ir.Call (dest, _, _) -> dest
  | Ir.Label _ | Ir.StoreGlobal _ | Ir.BranchZero _ | Ir.Jump _ | Ir.Return _ ->
      None

let transfer_exprs exprs instr =
  let exprs =
    match instr_dest instr with
    | None -> exprs
    | Some dest -> kill_exprs dest exprs
  in
  match expr_of_instr instr with
  | Some expr -> (
      match instr_dest instr with
      | Some dest when not (expr_depends_on dest expr) -> ExprMap.add expr dest exprs
      | _ -> exprs)
  | None -> exprs

let global_cse body =
  let cfg = Cfg.of_instrs body in
  let count = Array.length cfg.Cfg.instrs in
  let in_exprs = Array.make count ExprMap.empty in
  let out_exprs = Array.make count ExprMap.empty in
  let reachable = reachable_indices body in
  let changed = ref true in
  while !changed do
    changed := false;
    for index = 0 to count - 1 do
      if reachable.(index) then (
        let pred_exprs =
          cfg.Cfg.preds.(index)
          |> List.filter (fun pred -> reachable.(pred))
          |> List.map (fun pred -> out_exprs.(pred))
        in
        let in_expr =
          match pred_exprs with
          | [] -> ExprMap.empty
          | first :: rest -> List.fold_left intersect_exprs first rest
        in
        if not (exprs_equal in_expr in_exprs.(index)) then (
          in_exprs.(index) <- in_expr;
          changed := true);
        let out_expr = transfer_exprs in_expr cfg.Cfg.instrs.(index) in
        if not (exprs_equal out_expr out_exprs.(index)) then (
          out_exprs.(index) <- out_expr;
          changed := true))
    done
  done;
  cfg.Cfg.instrs
  |> Array.to_list
  |> List.mapi (fun index instr -> (index, instr))
  |> List.filter_map (fun (index, instr) ->
         if not reachable.(index) then None
         else
           match expr_of_instr instr with
           | Some expr -> (
               match (instr_dest instr, ExprMap.find_opt expr in_exprs.(index)) with
               | Some dest, Some source when source <> dest ->
                   Some (Ir.Move (dest, Ir.Reg source))
               | _ -> Some instr)
           | None -> Some instr)

let set_of_list values =
  List.fold_left (fun set value -> IntSet.add value set) IntSet.empty values

let all_indices count =
  List.init count (fun index -> index) |> set_of_list

let intersect_sets = function
  | [] -> IntSet.empty
  | first :: rest -> List.fold_left IntSet.inter first rest

let dominators cfg =
  let count = Array.length cfg.Cfg.instrs in
  let doms = Array.make count IntSet.empty in
  if count > 0 then (
    let all = all_indices count in
    for index = 0 to count - 1 do
      doms.(index) <- if index = 0 then IntSet.singleton 0 else all
    done;
    let changed = ref true in
    while !changed do
      changed := false;
      for index = 1 to count - 1 do
        let pred_doms = List.map (fun pred -> doms.(pred)) cfg.Cfg.preds.(index) in
        let next = IntSet.add index (intersect_sets pred_doms) in
        if not (IntSet.equal next doms.(index)) then (
          doms.(index) <- next;
          changed := true)
      done
    done);
  doms

let dominates doms dominator node =
  IntSet.mem dominator doms.(node)

let natural_loop cfg header latch =
  let rec visit seen = function
    | [] -> seen
    | node :: rest ->
        if IntSet.mem node seen then visit seen rest
        else visit (IntSet.add node seen) (cfg.Cfg.preds.(node) @ rest)
  in
  visit (IntSet.singleton header) [ latch ]

let loop_defs cfg nodes =
  IntSet.fold
    (fun node defs -> IntSet.union defs cfg.Cfg.defs.(node))
    nodes IntSet.empty

let pure_hoistable_instr = function
  | Ir.Move _ | Ir.Unary _ | Ir.ShiftLeft _ -> true
  | Ir.Binary (_, (Ast.Div | Ast.Mod), _, _) -> false
  | Ir.Binary _ -> true
  | Ir.LoadParam _ | Ir.LoadGlobal _ | Ir.StoreGlobal _ | Ir.Call _ | Ir.Label _
  | Ir.BranchZero _ | Ir.Jump _ | Ir.Return _ ->
      false

let loop_blocks_global_loads cfg nodes =
  IntSet.exists
    (fun node ->
      match cfg.Cfg.instrs.(node) with
      | Ir.StoreGlobal _ | Ir.Call _ -> true
      | _ -> false)
    nodes

let instr_operands = function
  | Ir.Move (_, operand) | Ir.Unary (_, _, operand)
  | Ir.ShiftLeft (_, operand, _) ->
      [ operand ]
  | Ir.Binary (_, _, lhs, rhs) -> [ lhs; rhs ]
  | Ir.Call (_, _, args) -> args
  | Ir.StoreGlobal (_, operand) | Ir.BranchZero (operand, _) | Ir.Return operand ->
      [ operand ]
  | Ir.LoadParam _ | Ir.LoadGlobal _ | Ir.Label _ | Ir.Jump _ -> []

let operand_invariant defs invariant_defs = function
  | Ir.Imm _ -> true
  | Ir.Reg reg -> (not (IntSet.mem reg defs)) || IntSet.mem reg invariant_defs

let definition_counts body =
  List.fold_left
    (fun counts instr ->
      match instr_dest instr with
      | None -> counts
      | Some dest ->
          let count = IntMap.find_opt dest counts |> Option.value ~default:0 in
          IntMap.add dest (count + 1) counts)
    IntMap.empty body

let single_definition counts reg =
  IntMap.find_opt reg counts |> Option.value ~default:0 = 1

let licm_once body =
  let cfg = Cfg.of_instrs body in
  let count = Array.length cfg.Cfg.instrs in
  let doms = dominators cfg in
  let def_counts = definition_counts body in
  let backedges =
    List.init count (fun index ->
        cfg.Cfg.succs.(index)
        |> List.filter_map (fun succ ->
               if dominates doms succ index then Some (succ, index) else None))
    |> List.concat
  in
  let try_loop (header, latch) =
    let nodes = natural_loop cfg header latch in
    let defs = loop_defs cfg nodes in
    let can_hoist_global_loads = not (loop_blocks_global_loads cfg nodes) in
    let invariant_defs = ref IntSet.empty in
    let hoisted = ref [] in
    let hoisted_indices = ref IntSet.empty in
    let changed = ref true in
    while !changed do
      changed := false;
      for index = 0 to count - 1 do
        if IntSet.mem index nodes && not (IntSet.mem index !hoisted_indices) then
          let instr = cfg.Cfg.instrs.(index) in
          match instr_dest instr with
          | Some dest
            when (pure_hoistable_instr instr
                 ||
                 match instr with
                 | Ir.LoadGlobal _ -> can_hoist_global_loads
                 | _ -> false)
                 && single_definition def_counts dest
                 && List.for_all (operand_invariant defs !invariant_defs)
                      (instr_operands instr) ->
              hoisted := (index, instr) :: !hoisted;
              hoisted_indices := IntSet.add index !hoisted_indices;
              invariant_defs := IntSet.add dest !invariant_defs;
              changed := true
          | _ -> ()
      done
    done;
    if !hoisted = [] then None
    else
      let hoisted =
        !hoisted |> List.sort (fun (lhs, _) (rhs, _) -> compare lhs rhs) |> List.map snd
      in
      Some (header, !hoisted_indices, hoisted)
  in
  match List.find_map try_loop backedges with
  | None -> body
  | Some (header, hoisted_indices, hoisted) ->
      cfg.Cfg.instrs
      |> Array.to_list
      |> List.mapi (fun index instr -> (index, instr))
      |> List.filter_map (fun (index, instr) ->
             if IntSet.mem index hoisted_indices then None
             else if index = header then Some (hoisted @ [ instr ])
             else Some [ instr ])
      |> List.concat

let licm body =
  let rec fix body =
    let next = licm_once body in
    if next = body then body else fix next
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
      |> rewrite_with_constants
      |> cleanup_control_flow
      |> global_cse
      |> licm
      |> eliminate_dead_defs
      |> eliminate_dead_stores
      |> cleanup_control_flow
    in
    if next = body then body else fix next
  in
  fix body

let max_reg_operand current = function
  | Ir.Imm _ -> current
  | Ir.Reg reg -> max current reg

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

let max_reg_body body =
  List.fold_left max_reg_instr (-1) body

let inline_blocker = function
  | Ir.Call _ | Ir.Label _ | Ir.BranchZero _ | Ir.Jump _ -> true
  | _ -> false

let inline_cost body =
  List.fold_left
    (fun cost -> function
      | Ir.LoadParam _ | Ir.Return _ -> cost
      | _ -> cost + 1)
    0 body

let inline_candidate (func : Ir.func) =
  func.Ir.name <> "main"
  && inline_cost func.Ir.body <= 8
  && not (List.exists inline_blocker func.Ir.body)

let build_inline_candidates funcs =
  List.fold_left
    (fun candidates func ->
      if inline_candidate func then StringMap.add func.Ir.name func candidates
      else candidates)
    StringMap.empty funcs

let subst_operand reg_values = function
  | Ir.Imm _ as imm -> imm
  | Ir.Reg reg -> (
      match IntMap.find_opt reg reg_values with
      | Some operand -> operand
      | None -> Diagnostic.fail "internal error: missing inline operand")

let inline_call next_reg (callee : Ir.func) dest args =
  let fresh () =
    let reg = !next_reg in
    incr next_reg;
    reg
  in
  let define reg operand reg_values =
    IntMap.add reg operand reg_values
  in
  let rec lower reg_values acc = function
    | [] -> List.rev acc
    | Ir.LoadParam (reg, index) :: rest ->
        let arg = List.nth args index in
        lower (define reg arg reg_values) acc rest
    | Ir.Move (reg, operand) :: rest ->
        let dest = fresh () in
        let operand = subst_operand reg_values operand in
        lower (define reg (Ir.Reg dest) reg_values) (Ir.Move (dest, operand) :: acc) rest
    | Ir.Unary (reg, op, operand) :: rest ->
        let dest = fresh () in
        let operand = subst_operand reg_values operand in
        lower (define reg (Ir.Reg dest) reg_values)
          (Ir.Unary (dest, op, operand) :: acc)
          rest
    | Ir.Binary (reg, op, lhs, rhs) :: rest ->
        let dest = fresh () in
        let lhs = subst_operand reg_values lhs in
        let rhs = subst_operand reg_values rhs in
        lower (define reg (Ir.Reg dest) reg_values)
          (Ir.Binary (dest, op, lhs, rhs) :: acc)
          rest
    | Ir.ShiftLeft (reg, operand, amount) :: rest ->
        let dest = fresh () in
        let operand = subst_operand reg_values operand in
        lower (define reg (Ir.Reg dest) reg_values)
          (Ir.ShiftLeft (dest, operand, amount) :: acc)
          rest
    | Ir.LoadGlobal (reg, name) :: rest ->
        let dest = fresh () in
        lower (define reg (Ir.Reg dest) reg_values)
          (Ir.LoadGlobal (dest, name) :: acc)
          rest
    | Ir.StoreGlobal (name, operand) :: rest ->
        let operand = subst_operand reg_values operand in
        lower reg_values (Ir.StoreGlobal (name, operand) :: acc) rest
    | Ir.Return operand :: _ ->
        let operand = subst_operand reg_values operand in
        let ret =
          match dest with
          | None -> []
          | Some dest -> move_or_nop dest operand
        in
        List.rev_append acc ret
    | (Ir.Call _ | Ir.Label _ | Ir.BranchZero _ | Ir.Jump _) :: _ ->
        Diagnostic.fail "internal error: unsupported inline instruction"
  in
  lower IntMap.empty [] callee.Ir.body

let inline_func candidates (func : Ir.func) =
  let next_reg = ref (max_reg_body func.Ir.body + 1) in
  let rec loop acc = function
    | [] -> List.rev acc
    | Ir.Call (dest, name, args) :: rest when name <> func.Ir.name -> (
        match StringMap.find_opt name candidates with
        | Some callee ->
            let instrs = inline_call next_reg callee dest args in
            loop (List.rev_append instrs acc) rest
        | None -> loop (Ir.Call (dest, name, args) :: acc) rest)
    | instr :: rest -> loop (instr :: acc) rest
  in
  { func with Ir.body = loop [] func.Ir.body }

let inline_round funcs =
  let candidates = build_inline_candidates funcs in
  funcs
  |> List.map (inline_func candidates)
  |> List.map (fun func -> { func with Ir.body = optimize_body func.Ir.body })

let rec inline_fix rounds funcs =
  if rounds = 0 then funcs
  else
    let next = inline_round funcs in
    if next = funcs then funcs else inline_fix (rounds - 1) next

let called_functions body =
  List.fold_left
    (fun calls -> function
      | Ir.Call (_, name, _) -> StringSet.add name calls
      | _ -> calls)
    StringSet.empty body

let remove_unreachable_funcs funcs =
  let funcs_by_name =
    List.fold_left
      (fun funcs_by_name (func : Ir.func) ->
        StringMap.add func.Ir.name func funcs_by_name)
      StringMap.empty funcs
  in
  let rec visit seen = function
    | [] -> seen
    | name :: rest ->
        if StringSet.mem name seen then visit seen rest
        else
          match StringMap.find_opt name funcs_by_name with
          | None -> visit seen rest
          | Some func ->
              let calls = called_functions func.Ir.body |> StringSet.elements in
              visit (StringSet.add name seen) (calls @ rest)
  in
  let reachable = visit StringSet.empty [ "main" ] in
  List.filter (fun (func : Ir.func) -> StringSet.mem func.Ir.name reachable) funcs

let split_params body =
  let rec loop params = function
    | Ir.LoadParam (dest, index) :: rest -> loop ((index, dest) :: params) rest
    | rest -> (List.sort compare params, rest)
  in
  loop [] body

let tail_loop_label name = ".L_" ^ name ^ "_tail_loop"

let rewrite_tail_recursion (func : Ir.func) =
  let params, rest = split_params func.Ir.body in
  if params = [] then func
  else
    let max_reg = max_reg_body func.Ir.body in
    let next_reg = ref (max_reg + 1) in
    let fresh () =
      let reg = !next_reg in
      incr next_reg;
      reg
    in
    let label = tail_loop_label func.Ir.name in
    let param_dests = List.map snd params in
    let rewrite_call args =
      if List.length args <> List.length param_dests then None
      else
        let temps = List.map (fun operand -> (fresh (), operand)) args in
        let save_args = List.map (fun (tmp, operand) -> Ir.Move (tmp, operand)) temps in
        let load_params =
          List.map2
            (fun param (tmp, _) -> Ir.Move (param, Ir.Reg tmp))
            param_dests temps
        in
        Some (save_args @ load_params @ [ Ir.Jump label ])
    in
    let rec rewrite acc = function
      | Ir.Call (Some ret, name, args) :: Ir.Return (Ir.Reg result) :: rest
        when name = func.Ir.name && ret = result -> (
          match rewrite_call args with
          | Some instrs -> rewrite (List.rev_append instrs acc) rest
          | None -> rewrite (Ir.Return (Ir.Reg result) :: Ir.Call (Some ret, name, args) :: acc) rest)
      | Ir.Call (None, name, args) :: Ir.Return operand :: rest when name = func.Ir.name -> (
          match rewrite_call args with
          | Some instrs -> rewrite (List.rev_append instrs acc) rest
          | None -> rewrite (Ir.Return operand :: Ir.Call (None, name, args) :: acc) rest)
      | instr :: rest -> rewrite (instr :: acc) rest
      | [] -> List.rev acc
    in
    let rewritten = rewrite [] rest in
    { func with Ir.body = List.map (fun (index, dest) -> Ir.LoadParam (dest, index)) params @ [ Ir.Label label ] @ rewritten }
let optimize_func func =
  let func = rewrite_tail_recursion func in
  { func with Ir.body = optimize_body func.Ir.body }

let run ~enabled (program : Ir.program) =
  if not enabled then program
  else
    let funcs =
      program.Ir.funcs
      |> List.map optimize_func
      |> inline_fix 4
      |> remove_unreachable_funcs
    in
    { program with Ir.funcs = funcs }
