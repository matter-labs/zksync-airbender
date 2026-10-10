import Airbender.Proofs.Trace.SailHistory

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

end Airbender.Trace.Proofs
