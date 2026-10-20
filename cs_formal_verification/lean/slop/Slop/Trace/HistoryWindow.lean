import Slop.Delegation.CallGroups
import Slop.Trace.RowHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail
set_option warningAsError true

theorem history_window {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events before after) {low high : Nat} (bounds : low ≤ high) :
    ∃ start finish,
      events = (events.filter fun event => decide (high < event.1)) ++
        (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ high)) ++
        (events.filter fun event => decide (event.1 ≤ low)) ∧
      SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) before start ∧
      SailHistory cells (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ high)) start finish ∧
      SailHistory cells (events.filter fun event => decide (high < event.1)) finish after := by
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
  obtain ⟨finish, past, future⟩ := sail_history_append.mp (outer.symm ▸ history)
  obtain ⟨start, earlier, current⟩ := sail_history_append.mp past
  exact ⟨start, finish, by simpa only [List.append_assoc] using outer.symm, earlier, current, future⟩

theorem history_without_zero {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) :
    SailHistory cells (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after := by
  induction history with
  | nil => exact .nil _
  | @cons event rest before middle after past cell member address read written ih =>
    by_cases zero : event.2.1 = (Cell.register 0).addressCode
    · have equal : cell = Cell.register 0 := cell_address_injective (address.trans zero)
      subst cell
      have noEffect : Reference.Sail.run ((Cell.register 0).write (memoryWord event.2.2.2)) middle = .ok () middle := rfl
      have same := (EStateM.Result.ok.inj (noEffect.symm.trans written)).2
      subst after
      simpa only [List.filter_cons, zero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false] using ih
    · simpa only [List.filter_cons, zero, ne_eq, not_false_eq_true, decide_true, ite_true] using
        (SailHistory.cons ih cell member address read written)

end Airbender.Trace.Proofs
