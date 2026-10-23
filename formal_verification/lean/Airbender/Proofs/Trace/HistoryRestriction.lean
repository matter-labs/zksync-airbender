import Airbender.Proofs.Trace.HistoryWindow

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail
set_option warningAsError true

theorem history_restriction {cells : List Cell} {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after) (keep : Nat → Bool)
    (selected : ∀ event ∈ events, keep event.2.1 = true) :
    SailHistory (cells.filter fun cell => keep cell.addressCode) events before after := by
  induction history with
  | nil => exact .nil _
  | @cons event rest initial middle finalState past cell member address read written ih =>
    refine .cons (ih (fun previous present => selected previous (List.mem_cons_of_mem event present))) cell ?_ address read written
    exact List.mem_filter.mpr ⟨member, address ▸ selected event (List.mem_cons_self)⟩

theorem history_worker_cells {cells : List Cell} {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after) :
    SailHistory (cells.filter fun cell => cell.addressCode != (Cell.register 0).addressCode)
      (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after := by
  apply history_restriction (history_without_zero history) (fun address => address != (Cell.register 0).addressCode)
  intro event member
  exact bne_iff_ne.mpr (of_decide_eq_true (List.mem_filter.mp member).2)

end Airbender.Trace.Proofs
