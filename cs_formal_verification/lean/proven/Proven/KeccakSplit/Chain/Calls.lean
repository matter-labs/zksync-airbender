module
public import Proven.KeccakSplit.Chain.Paths
public import Proven.Blake2Round.DiagonalG
public import Proven.Blake2Round.FinalXor
public import Proven.KeccakSplit.Memory.History
public import Mathlib.Tactic

@[expose] public section

/- A complete initialized request: the control path orders the 361 rows, the Sail
   history splits into one atomic group per row, and each row executes its call
   between consecutive group boundaries. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- Every lane slot 0..29 is accessed by some call. -/
theorem slot_coverage : ∀ slot : Fin 30, ∃ index : Fin 361, ∃ lane : Fin 7,
    lane.val < Call.slotCount (kindAt index.val) ∧ ((Call.slots index)[lane]).val = slot.val := by
  decide +kernel

theorem port_time (row : Row p) {port : MemoryPort} (present : port ∈ row.ports) :
    (transferEvent (readToken row.assignment port, row.writeToken port)).1 =
      (timeOfPair (controlEdge row).2.time).value + 1 := by
  have same : (row.writeToken port).time = (row.writeToken (controlPort row.kind)).time := by
    change (_, _) = (_, _)
    rw [port_offset row present, port_offset row (control_port_member row)]
  simp only [transferEvent, controlEdge, same]

theorem get_index_eq {α : Type} {l : List α} {a b : Nat} (same : a = b) {ha : a < l.length}
    {hb : b < l.length} : l[a]'ha = l[b]'hb := by
  subst same; rfl

theorem readWord_eq (row : Row p) {index : Nat} (bound : index < row.ports.size) :
    row.readWord index = (readToken row.assignment row.ports[index]).word := by
  simp [Row.readWord, bound]

/-- Ports 0 and 1 of every worker are x10 and x11. -/
theorem register_ports (row : Row p) :
    (∃ bound : 0 < row.ports.size, (row.ports[0]).address = .constantRegister 10) ∧
      (∃ bound : 1 < row.ports.size, (row.ports[1]).address = .constantRegister 11) := by
  cases row with
  | mk kind w =>
    cases kind <;>
      exact ⟨⟨by simp only [Row.ports]; decide, rfl⟩, ⟨by simp only [Row.ports]; decide, rfl⟩⟩

end Airbender.Keccak.Split.Native.Proofs
