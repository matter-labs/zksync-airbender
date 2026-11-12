module
public import Proven.UnifiedReduced.RVCaller.HistoryWindow

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Trace.Proofs
set_option warningAsError true

/-- Actual writes through the upper cut are precisely the current cycle and its
    prefix. No ordering of simultaneous writes is supplied independently. -/
theorem history_prefix_of_window {cells : List Cell} {events : List MemoryAccess}
    {initial before after : RV.State} {low high : Nat}
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (bounds : low ≤ high)
    (past : RVHistory cells (events.filter fun event => decide (event.1 ≤ low)) initial before)
    (current : RVHistory cells (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ high)) before after) :
    RVHistory cells (events.filter fun event => decide (event.1 ≤ high)) initial after := by
  have split := Delegation.Proofs.split_clock (events.filter fun event => decide (event.1 ≤ high))
    (ordered.sublist List.filter_sublist) (low + 1)
  have newer : ((events.filter fun event => decide (event.1 ≤ high)).filter
      fun event => decide (low + 1 ≤ event.1)) =
      events.filter (fun event => decide (low < event.1 ∧ event.1 ≤ high)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have older : ((events.filter fun event => decide (event.1 ≤ high)).filter
      fun event => decide (event.1 < low + 1)) =
      events.filter (fun event => decide (event.1 ≤ low)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [newer, older] at split
  rw [← split]
  exact rv_history_append.mpr ⟨before, past, current⟩

end Airbender.Trace.Machine.Proofs
