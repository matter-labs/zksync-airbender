import Slop.Trace.SailHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail
set_option warningAsError true

theorem history_cell_frame {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (other : Cell) (otherAligned : other.Aligned)
    (untouched : ∀ event ∈ events, event.2.1 ≠ other.addressCode)
    {value : BitVec 32} (read : other.read before = .ok value before) :
    other.read after = .ok value after := by
  induction history with
  | nil => exact read
  | @cons event rest before middle after past cell member address old written ih =>
    have earlier := ih (fun e m => untouched e (List.mem_cons_of_mem _ m)) read
    apply cell_write_frame written _ (aligned cell member) otherAligned earlier
    intro same
    exact untouched event List.mem_cons_self (by rw [same, address])

theorem history_cells_readable {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ cell ∈ cells, ∃ value, cell.read after = .ok value after := by
  induction history with
  | nil => exact initial
  | @cons event rest before middle after past cell member address old written ih =>
    have earlier := ih initial
    intro other present
    by_cases zero : other = Cell.register 0
    · exact ⟨0, by rw [zero]; rfl⟩
    by_cases same : other = cell
    · subst other
      obtain ⟨result, actual, read⟩ := cell_write_readback cell (memoryWord event.2.2.2) middle
        (fun equal => False.elim (zero equal))
      have same := (EStateM.Result.ok.inj (actual.symm.trans written)).2
      exact ⟨_, same ▸ read⟩
    · obtain ⟨value, read⟩ := earlier other present
      exact ⟨value, cell_write_frame written same (aligned cell member) (aligned other present) read⟩

end Airbender.Trace.Proofs
