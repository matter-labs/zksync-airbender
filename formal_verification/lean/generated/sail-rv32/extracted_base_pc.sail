// Extracted verbatim from the pinned normal F_Base path.
val normal_base_next_pc : unit -> unit
function normal_base_next_pc() = {
  nextPC = PC + 4;
  ()
}
