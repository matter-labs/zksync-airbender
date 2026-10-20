import Slop.Trace.MemoryFrame

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem history_readable {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (_noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ cell ∈ cells, ∃ value, cell.read after = .ok value after :=
  history_cells_readable history aligned initial

theorem atomic_observations {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before)
    (distinct : (events.map fun event => event.2.1).Nodup) :
    ∀ event ∈ events, ∃ cell ∈ cells, cell.addressCode = event.2.1 ∧
      cell.read before = .ok (memoryWord event.2.2.1) before ∧
      cell.read after = .ok (memoryWord event.2.2.2) after := by
  induction history with
  | nil => intro event member; cases member
  | @cons event rest before middle after past cell member address old written ih =>
    have unique := List.nodup_cons.mp distinct
    have untouched : ∀ other ∈ rest, other.2.1 ≠ cell.addressCode := by
      intro other present same
      exact unique.1 (List.mem_map.mpr ⟨other, present, same.trans address⟩)
    have tail := ih (fun e m => noZero e (List.mem_cons_of_mem _ m)) initial unique.2
    intro other included
    rcases List.mem_cons.mp included with same | included
    · subst other
      obtain ⟨value, actual⟩ := initial cell member
      have read := history_cell_frame past aligned cell (aligned cell member) untouched actual
      have valueEqual := (EStateM.Result.ok.inj (read.symm.trans old)).1
      subst value
      obtain ⟨result, execution, readback⟩ := cell_write_readback cell (memoryWord event.2.2.2) middle (by
        intro zero
        exact False.elim (noZero event List.mem_cons_self (by rw [← address, zero])))
      have same := (EStateM.Result.ok.inj (execution.symm.trans written)).2
      exact ⟨cell, member, address, actual, same ▸ readback⟩
    · obtain ⟨actual, present, code, read, result⟩ := tail other included
      have different : actual ≠ cell := by
        intro same
        exact untouched other included (by rw [← code, same])
      exact ⟨actual, present, code, read,
        cell_write_frame written different (aligned cell member) (aligned actual present) result⟩

end Airbender.Delegation.Proofs
