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

let leaf_extra_regs = [ "t3"; "t4"; "t5" ]

let has_call body =
  List.exists
    (function
      | Ir.Call _ -> true
      | _ -> false)
    body

let allocatable_regs func =
  if has_call func.Ir.body then callee_saved_regs else leaf_extra_regs @ callee_saved_regs

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

let choose_location regs preferences used_phys spill_slot reg neighbors allocation =
  let unavailable =
    IntSet.fold
      (fun neighbor used ->
        match IntMap.find_opt neighbor allocation with
        | Some (Phys reg) -> StringSet.add reg used
        | _ -> used)
      neighbors StringSet.empty
  in
  let preferred =
    IntMap.find_opt reg preferences
    |> Option.value ~default:[]
    |> List.find_map (fun preferred ->
           match IntMap.find_opt preferred allocation with
           | Some (Phys phys)
             when List.mem phys regs && not (StringSet.mem phys unavailable) ->
               Some phys
           | _ -> None)
  in
  match
    match preferred with
    | Some phys -> Some phys
    | None -> List.find_opt (fun reg -> not (StringSet.mem reg unavailable)) regs
  with
  | Some reg -> (Phys reg, StringSet.add reg used_phys, spill_slot)
  | None -> (Stack spill_slot, used_phys, spill_slot + 1)

let allocate func =
  let regs = allocatable_regs func in
  let _, _, graph = build_graph func in
  let preferences = move_preferences func.Ir.body in
  let nodes =
    graph
    |> IntMap.bindings
    |> List.sort (fun (_, lhs) (_, rhs) ->
           compare (IntSet.cardinal rhs) (IntSet.cardinal lhs))
  in
  let locations, used_phys, stack_slots =
    List.fold_left
      (fun (allocation, used_phys, spill_slot) (reg, neighbors) ->
        let location, used_phys, spill_slot =
          choose_location regs preferences used_phys spill_slot reg neighbors allocation
        in
        (IntMap.add reg location allocation, used_phys, spill_slot))
      (IntMap.empty, StringSet.empty, 0) nodes
  in
  let used_regs =
    callee_saved_regs
    |> List.filter (fun reg -> StringSet.mem reg used_phys)
  in
  { locations; stack_slots; used_regs }
