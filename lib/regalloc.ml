module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)
module StringSet = Set.Make (String)

type location =
  | Phys of string
  | Stack of int

type allocation = {
  locations : location IntMap.t;
  stack_slots : int;
  used_regs : string list;
}

let callee_saved_regs =
  [ "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11" ]

let arg_regs = [ "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" ]

let leaf_temp_regs = [ "t3"; "t4"; "t5" ]

let has_call body =
  List.exists
    (function
      | Ir.Call _ -> true
      | _ -> false)
    body

let max_param_index body =
  List.fold_left
    (fun current -> function
      | Ir.LoadParam (_, index) -> max current index
      | _ -> current)
    (-1) body

let incoming_arg_reg index =
  if index < List.length arg_regs then Some (List.nth arg_regs index) else None

let arg_reg_index phys =
  arg_regs
  |> List.mapi (fun index reg -> (index, reg))
  |> List.find_map (fun (index, reg) -> if reg = phys then Some index else None)

let param_reg_preferences body =
  List.fold_left
    (fun preferences -> function
      | Ir.LoadParam (dest, index) -> (
          match incoming_arg_reg index with
          | Some phys -> IntMap.add dest phys preferences
          | None -> preferences)
      | _ -> preferences)
    IntMap.empty body

let return_reg_preferences body =
  List.fold_left
    (fun preferences -> function
      | Ir.Return (Ir.Reg reg) -> IntMap.add reg "a0" preferences
      | _ -> preferences)
    IntMap.empty body

let leaf_extra_regs func =
  ignore func;
  arg_regs @ leaf_temp_regs

let allocatable_regs func =
  if has_call func.Ir.body then leaf_temp_regs @ callee_saved_regs
  else leaf_extra_regs func @ callee_saved_regs

let location allocation vreg =
  match IntMap.find_opt vreg allocation.locations with
  | Some location -> location
  | None -> Stack 0

let add_node graph reg =
  if IntMap.mem reg graph then graph else IntMap.add reg IntSet.empty graph

let add_edge graph lhs rhs =
  if lhs = rhs then graph
  else
    let graph = add_node (add_node graph lhs) rhs in
    let lhs_neighbors =
      IntMap.find lhs graph |> IntSet.add rhs
    in
    let rhs_neighbors =
      IntMap.find rhs graph |> IntSet.add lhs
    in
    graph
    |> IntMap.add lhs lhs_neighbors
    |> IntMap.add rhs rhs_neighbors

let add_preference lhs rhs preferences =
  if lhs = rhs then preferences
  else
    let add_one key value preferences =
      let values = IntMap.find_opt key preferences |> Option.value ~default:[] in
      IntMap.add key (value :: values) preferences
    in
    preferences |> add_one lhs rhs |> add_one rhs lhs

let move_preferences body =
  List.fold_left
    (fun preferences -> function
      | Ir.Move (dest, Ir.Reg source) -> add_preference dest source preferences
      | _ -> preferences)
    IntMap.empty body

let all_vregs (cfg : Cfg.t) =
  Array.fold_left
    (fun regs set -> IntSet.union regs set)
    IntSet.empty cfg.uses
  |> fun regs ->
  Array.fold_left
    (fun regs set -> IntSet.union regs set)
    regs cfg.defs

let build_graph func =
  let cfg = Cfg.of_instrs func.Ir.body in
  let liveness = Liveness.analyze cfg in
  let graph =
    IntSet.fold (fun reg graph -> add_node graph reg) (all_vregs cfg) IntMap.empty
  in
  let graph = ref graph in
  for index = 0 to Array.length cfg.defs - 1 do
    graph :=
      IntSet.fold
        (fun def graph ->
          IntSet.fold (fun live graph -> add_edge graph def live) liveness.live_out.(index) graph)
        cfg.defs.(index) !graph
  done;
  let graph = !graph in
  (cfg, liveness, graph)

let set_of_list values =
  List.fold_left (fun set value -> IntSet.add value set) IntSet.empty values

let all_indices count =
  List.init count (fun index -> index) |> set_of_list

let intersect_sets = function
  | [] -> IntSet.empty
  | first :: rest -> List.fold_left IntSet.inter first rest

let dominators (cfg : Cfg.t) =
  let count = Array.length cfg.instrs in
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
        let pred_doms = List.map (fun pred -> doms.(pred)) cfg.preds.(index) in
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

let loop_depths (cfg : Cfg.t) =
  let count = Array.length cfg.instrs in
  let depths = Array.make count 0 in
  let doms = dominators cfg in
  for index = 0 to count - 1 do
    List.iter
      (fun succ ->
        if dominates doms succ index then
          natural_loop cfg succ index
          |> IntSet.iter (fun node -> depths.(node) <- depths.(node) + 1))
      cfg.succs.(index)
  done;
  depths

let instr_uses_defs instr =
  let uses, defs = Cfg.instr_uses_defs instr in
  IntSet.union uses defs

let add_weight reg amount weights =
  let current = IntMap.find_opt reg weights |> Option.value ~default:0 in
  IntMap.add reg (current + amount) weights

let reg_weights (cfg : Cfg.t) =
  let depths = loop_depths cfg in
  Array.fold_left
    (fun (index, weights) instr ->
      let amount = 1 + (10 * depths.(index)) in
      let regs = instr_uses_defs instr in
      ( index + 1,
        IntSet.fold (fun reg weights -> add_weight reg amount weights) regs weights
      ))
    (0, IntMap.empty) cfg.instrs
  |> snd

let call_live_regs cfg liveness =
  Array.fold_left
    (fun (index, regs) instr ->
      match instr with
      | Ir.Call _ ->
          let live_across_call =
            IntSet.diff liveness.Liveness.live_out.(index) cfg.Cfg.defs.(index)
          in
          (index + 1, IntSet.union regs live_across_call)
      | _ -> (index + 1, regs))
    (0, IntSet.empty) cfg.Cfg.instrs
  |> snd

let caller_saved_candidate phys vreg call_live =
  List.mem phys leaf_temp_regs && not (IntSet.mem vreg call_live)

let choose_location regs param_count param_regs return_regs preferences call_live used_phys spill_slot reg neighbors allocation =
  let usable phys =
    ((not (List.mem phys leaf_temp_regs)) || caller_saved_candidate phys reg call_live)
    &&
    match arg_reg_index phys with
    | None -> true
    | Some index -> (
        match IntMap.find_opt reg param_regs with
        | Some preferred -> preferred = phys
        | None -> index >= param_count || IntMap.find_opt reg return_regs = Some phys)
  in
  let param_preferred =
    match IntMap.find_opt reg param_regs with
    | Some phys when List.mem phys regs -> Some phys
    | _ -> None
  in
  let return_preferred =
    match IntMap.find_opt reg return_regs with
    | Some preferred when List.mem preferred regs -> Some preferred
    | _ -> None
  in
  let unavailable =
    IntSet.fold
      (fun neighbor used ->
        match IntMap.find_opt neighbor allocation with
        | Some (Phys reg) -> StringSet.add reg used
        | _ -> used)
      neighbors StringSet.empty
  in
  let preferred =
    match param_preferred with
    | Some phys when usable phys && not (StringSet.mem phys unavailable) ->
        Some phys
    | _ ->
        (match return_preferred with
        | Some phys when usable phys && not (StringSet.mem phys unavailable) ->
            Some phys
        | _ ->
            IntMap.find_opt reg preferences
            |> Option.value ~default:[]
            |> List.find_map (fun preferred ->
                   match IntMap.find_opt preferred allocation with
                   | Some (Phys phys)
                     when List.mem phys regs
                          && usable phys
                          && not (StringSet.mem phys unavailable) ->
                       Some phys
                   | _ -> None))
  in
  match
    match preferred with
    | Some phys -> Some phys
    | None ->
        List.find_opt
          (fun phys -> usable phys && not (StringSet.mem phys unavailable))
          regs
  with
  | Some reg -> (Phys reg, StringSet.add reg used_phys, spill_slot)
  | None -> (Stack spill_slot, used_phys, spill_slot + 1)

let allocate func =
  let regs = allocatable_regs func in
  let cfg, liveness, graph = build_graph func in
  let param_count = max_param_index func.Ir.body + 1 in
  let param_regs = param_reg_preferences func.Ir.body in
  let preferences = move_preferences func.Ir.body in
  let weights = reg_weights cfg in
  let weight reg = IntMap.find_opt reg weights |> Option.value ~default:0 in
  let return_regs =
    return_reg_preferences func.Ir.body
    |> IntMap.filter (fun reg _ -> weight reg <= 4)
  in
  let call_live = call_live_regs cfg liveness in
  let nodes =
    graph
    |> IntMap.bindings
    |> List.sort (fun (lhs_reg, lhs_neighbors) (rhs_reg, rhs_neighbors) ->
           let weight_order = compare (weight rhs_reg) (weight lhs_reg) in
           if weight_order <> 0 then weight_order
           else
             compare (IntSet.cardinal rhs_neighbors)
               (IntSet.cardinal lhs_neighbors))
  in
  let locations, used_phys, stack_slots =
    List.fold_left
      (fun (allocation, used_phys, spill_slot) (reg, neighbors) ->
        let location, used_phys, spill_slot =
          choose_location regs param_count param_regs return_regs preferences call_live
            used_phys spill_slot reg neighbors allocation
        in
        (IntMap.add reg location allocation, used_phys, spill_slot))
      (IntMap.empty, StringSet.empty, 0) nodes
  in
  let used_regs =
    callee_saved_regs
    |> List.filter (fun reg -> StringSet.mem reg used_phys)
  in
  { locations; stack_slots; used_regs }
