import Slop.Delegation.CallGroups
import Slop.Trace.RowHistory
import Slop.Trace.RVHistory
import Slop.Trace.RVCells

namespace Airbender.Trace.Proofs
set_option warningAsError true

theorem rv_history_window {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells events before after) {low high : Nat} (bounds : low ≤ high) :
    ∃ start finish,
      events = (events.filter fun event => decide (high < event.1)) ++
        (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ high)) ++
        (events.filter fun event => decide (event.1 ≤ low)) ∧
      RVHistory cells (events.filter fun event => decide (event.1 ≤ low)) before start ∧
      RVHistory cells (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ high)) start finish ∧
      RVHistory cells (events.filter fun event => decide (high < event.1)) finish after := by
  have outer := Delegation.Proofs.split_clock events ordered (high + 1)
  have inner := Delegation.Proofs.split_clock (events.filter fun event => decide (event.1 < high + 1))
    (ordered.sublist List.filter_sublist) (low + 1)
  have newer : (events.filter fun event => decide (high + 1 ≤ event.1)) =
      (events.filter fun event => decide (high < event.1)) := by
    apply List.filter_congr
    intro event _
    simp only [decide_eq_decide]
    omega
  have current : ((events.filter fun event => decide (event.1 < high + 1)).filter
      fun event => decide (low + 1 ≤ event.1)) =
      (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ high)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have older : ((events.filter fun event => decide (event.1 < high + 1)).filter
      fun event => decide (event.1 < low + 1)) =
      (events.filter fun event => decide (event.1 ≤ low)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [current, older] at inner
  rw [newer, ← inner] at outer
  obtain ⟨finish, past, future⟩ := rv_history_append.mp (outer.symm ▸ history)
  obtain ⟨start, earlier, current⟩ := rv_history_append.mp past
  exact ⟨start, finish, by simpa only [List.append_assoc] using outer.symm, earlier, current, future⟩

/-- RV sibling of `history_without_zero`: dropping x0 accesses that write zero keeps the RV history (an x0 write of 0
    reads back 0, so `Cell.applyRV` leaves the state unchanged). -/
theorem rv_history_without_zero {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0) :
    RVHistory cells (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after := by
  induction history with
  | nil => exact .nil _
  | @cons event rest before middle after past cell member address read written ih =>
    have tail := ih (fun other present => zero other (List.mem_cons_of_mem _ present))
    by_cases isZero : event.2.1 = (Cell.register 0).addressCode
    · have equal : cell = Cell.register 0 := cell_address_injective (address.trans isZero)
      subst cell
      have value := zero event List.mem_cons_self isZero
      have readZero : (Cell.register 0).readRV middle = some 0 := by
        simp [Cell.readRV, RV.State.getReg]
      have same : after = middle := by
        rw [value] at written
        simp only [Cell.applyRV, readZero, ite_true, Option.some.injEq] at written
        exact written.symm
      subst after
      simpa only [List.filter_cons, isZero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
        using tail
    · simpa only [List.filter_cons, isZero, ne_eq, not_false_eq_true, decide_true, ite_true] using
        (RVHistory.cons tail cell member address read written)

end Airbender.Trace.Proofs
