import Airbender.Proofs.Trace.MemoryFrame

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- A single access to one address reads its initial Sail value. Other
addresses may repeat. Their aligned writes preserve this cell's value. -/
theorem history_unique_address_read {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before)
    (target : MemoryAccess)
    (single : (events.filter fun event => decide (event.2.1 = target.2.1)) = [target]) :
    ∃ cell ∈ cells, cell.addressCode = target.2.1 ∧
      cell.read before = .ok (memoryWord target.2.2.1) before := by
  induction history with
  | nil => simp at single
  | @cons event rest before middle after past cell member address old written ih =>
    by_cases same : event.2.1 = target.2.1
    · have picked : event :: (rest.filter fun other => decide (other.2.1 = target.2.1)) = [target] := by
        simpa only [List.filter_cons, same, decide_true, if_true] using single
      have equal := (List.cons.inj picked).1
      have empty := (List.cons.inj picked).2
      subst target
      have untouched : ∀ other ∈ rest, other.2.1 ≠ cell.addressCode := by
        intro other included equal
        have present : other ∈ rest.filter (fun source => decide (source.2.1 = event.2.1)) :=
          List.mem_filter.mpr ⟨included, decide_eq_true (equal.trans address)⟩
        rw [empty] at present
        exact List.not_mem_nil present
      obtain ⟨value, read⟩ := initial cell member
      have framed := history_cell_frame past aligned cell (aligned cell member) untouched read
      have valueEqual := (EStateM.Result.ok.inj (framed.symm.trans old)).1
      subst value
      exact ⟨cell, member, address, read⟩
    · have tailSingle : (rest.filter fun other => decide (other.2.1 = target.2.1)) = [target] := by
        simpa only [List.filter_cons, same, decide_false, Bool.false_eq_true, if_false] using single
      exact ih initial tailSingle

end Airbender.Trace.Proofs
