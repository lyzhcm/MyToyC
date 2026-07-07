module IntSet = Set.Make (Int)

type live_set = IntSet.t

type t = {
  live_in : live_set array;
  live_out : live_set array;
}

let analyze (cfg : Cfg.t) =
  let count = Array.length cfg.instrs in
  let live_in = Array.make count IntSet.empty in
  let live_out = Array.make count IntSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for index = count - 1 downto 0 do
      let out_set =
        List.fold_left
          (fun acc succ -> IntSet.union acc live_in.(succ))
          IntSet.empty cfg.succs.(index)
      in
      let in_set =
        IntSet.union cfg.uses.(index)
          (IntSet.diff out_set cfg.defs.(index))
      in
      if not (IntSet.equal out_set live_out.(index)) then (
        live_out.(index) <- out_set;
        changed := true);
      if not (IntSet.equal in_set live_in.(index)) then (
        live_in.(index) <- in_set;
        changed := true)
    done
  done;
  { live_in; live_out }
