import Airbender.Proofs.Trace.MemoryFrame

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem history_cell_copy_frame {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (target : Cell)
    (targetAligned : target.Aligned) (nonzero : target ≠ Cell.register 0)
    (copies : ∀ event ∈ events, event.2.1 = target.addressCode →
      memoryWord event.2.2.1 = memoryWord event.2.2.2)
    {value : BitVec 32} (read : target.read before = .ok value before) :
    target.read after = .ok value after := by
  induction history with
  | nil => exact read
  | @cons event rest before middle after past cell member address old written ih =>
    have earlier := ih (fun e present => copies e (List.mem_cons_of_mem _ present)) read
    by_cases same : target = cell
    · subst target
      have equal := (EStateM.Result.ok.inj (earlier.symm.trans old)).1.trans
        (copies event List.mem_cons_self address.symm)
      obtain ⟨result, actual, readback⟩ := cell_write_readback cell
        (memoryWord event.2.2.2) middle (fun zero => False.elim (nonzero zero))
      have stateEqual := (EStateM.Result.ok.inj (actual.symm.trans written)).2
      subst result
      simpa only [← equal] using readback
    · exact cell_write_frame written same (aligned cell member) targetAligned earlier

end Airbender.Delegation.Proofs
