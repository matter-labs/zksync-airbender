import Slop.Delegation.Terminal

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true

theorem split_clock (events : List MemoryAccess)
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (cut : Nat) :
    (events.filter fun event => decide (cut ≤ event.1)) ++
      (events.filter fun event => decide (event.1 < cut)) = events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have tail := List.pairwise_cons.mp ordered
    by_cases recent : cut ≤ event.1
    · simp only [List.filter_cons, recent, Nat.not_lt.mpr recent, decide_false]
      exact congrArg (List.cons event) (ih tail.2)
    · have old : ∀ next ∈ rest, next.1 < cut := by
        intro next member
        have less := tail.1 next member
        omega
      have noRecent : (rest.filter fun next => decide (cut ≤ next.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro next member
        simp only [decide_eq_true_eq]
        exact Nat.not_le.mpr (old next member)
      have oldTail : (rest.filter fun next => decide (next.1 < cut)) = rest := by
        apply List.filter_eq_self.mpr
        intro next member
        simpa only [decide_eq_true_eq] using old next member
      simp [recent, Nat.lt_of_not_ge recent, noRecent, oldTail]

theorem group_call_events {rows : List α} {events : List MemoryAccess} (clock : α → Nat)
    (rowOrder : rows.Pairwise (fun a b => clock b < clock a))
    (eventOrder : events.Pairwise (fun a b => b.1 ≤ a.1))
    (coverage : ∀ event ∈ events, ∃ row ∈ rows, event.1 = clock row) :
    rows.flatMap (fun row => events.filter fun event => decide (event.1 = clock row)) = events := by
  induction rows generalizing events with
  | nil =>
    have empty : events = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro event member
      obtain ⟨row, present, _⟩ := coverage event member
      simp at present
    simp [empty]
  | cons first rest ih =>
    have rows := List.pairwise_cons.mp rowOrder
    have upper : ∀ event ∈ events, event.1 ≤ clock first := by
      intro event member
      obtain ⟨row, present, same⟩ := coverage event member
      rcases List.mem_cons.mp present with rfl | present
      · exact same.le
      · exact Nat.le_of_lt (same ▸ rows.1 row present)
    let older := events.filter fun event => decide (event.1 < clock first)
    have coverageOld : ∀ event ∈ older, ∃ row ∈ rest, event.1 = clock row := by
      intro event member
      obtain ⟨present, less⟩ := List.mem_filter.mp member
      have less : event.1 < clock first := by simpa only [decide_eq_true_eq] using less
      obtain ⟨row, included, same⟩ := coverage event present
      rcases List.mem_cons.mp included with equal | included
      · subst row
        omega
      · exact ⟨row, included, same⟩
    have grouped := ih rows.2 (eventOrder.sublist List.filter_sublist) coverageOld
    have filters : ∀ row ∈ rest,
        (older.filter fun event => decide (event.1 = clock row)) =
          (events.filter fun event => decide (event.1 = clock row)) := by
      intro row member
      have below := rows.1 row member
      have within : ((events.filter fun event => decide (event.1 = clock row)).filter
          fun event => decide (event.1 < clock first)) =
          (events.filter fun event => decide (event.1 = clock row)) := by
        apply List.filter_eq_self.mpr
        intro event present
        have same : event.1 = clock row := by
          simpa only [decide_eq_true_eq] using (List.mem_filter.mp present).2
        simpa only [decide_eq_true_eq, same] using below
      change ((events.filter _).filter _) = _
      rw [List.filter_filter]
      rw [List.filter_filter] at within
      simpa only [Bool.and_comm] using within
    have lowerGroups : rest.flatMap (fun row => events.filter fun event => decide (event.1 = clock row)) = older := by
      calc
        rest.flatMap (fun row => events.filter fun event => decide (event.1 = clock row)) =
            rest.flatMap (fun row => older.filter fun event => decide (event.1 = clock row)) := by
          change (rest.map _).flatten = (rest.map _).flatten
          apply congrArg List.flatten
          apply List.map_congr_left
          intro row member
          exact (filters row member).symm
        _ = older := grouped
    have latest : (events.filter fun event => decide (clock first ≤ event.1)) =
        (events.filter fun event => decide (event.1 = clock first)) := by
      apply List.filter_congr
      intro event member
      have bound := upper event member
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    rw [List.flatMap_cons, lowerGroups, ← latest]
    exact split_clock events eventOrder (clock first)

theorem call_group_perm {rows : List α} {events : List MemoryAccess}
    (clock : α → Nat) (accesses : α → List MemoryAccess)
    (unique : (rows.map clock).Nodup) (permutation : events.Perm (rows.flatMap accesses))
    (times : ∀ row ∈ rows, ∀ event ∈ accesses row, event.1 = clock row)
    {row : α} (present : row ∈ rows) :
    (events.filter fun event => decide (event.1 = clock row)).Perm (accesses row) := by
  have projected := permutation.filter (fun event => decide (event.1 = clock row))
  have selected : ((rows.flatMap accesses).filter fun event => decide (event.1 = clock row)) = accesses row := by
    clear permutation events projected
    induction rows with
    | nil => simp at present
    | cons first rest ih =>
      have clocks := List.nodup_cons.mp unique
      rw [List.flatMap_cons, List.filter_append]
      rcases List.mem_cons.mp present with equal | member
      · subst row
        have firstAll : ((accesses first).filter fun event => decide (event.1 = clock first)) = accesses first := by
          apply List.filter_eq_self.mpr
          intro event member
          simpa only [decide_eq_true_eq] using times first List.mem_cons_self event member
        have restNone : ((rest.flatMap accesses).filter fun event => decide (event.1 = clock first)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro event member
          obtain ⟨later, included, eventMember⟩ := List.mem_flatMap.mp member
          have time := times later (List.mem_cons_of_mem _ included) event eventMember
          have unequal : clock later ≠ clock first := by
            intro same
            exact clocks.1 (List.mem_map.mpr ⟨later, included, same⟩)
          simp only [decide_eq_true_eq, time, unequal]
          simp
        rw [firstAll, restNone, List.append_nil]
      · have unequal : clock first ≠ clock row := by
          intro same
          exact clocks.1 (List.mem_map.mpr ⟨row, member, same.symm⟩)
        have firstNone : ((accesses first).filter fun event => decide (event.1 = clock row)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro event included
          have time := times first List.mem_cons_self event included
          simp only [decide_eq_true_eq, time, unequal]
          simp
        rw [firstNone, List.nil_append]
        exact ih clocks.2 (fun later included => times later (List.mem_cons_of_mem _ included)) member
  exact selected ▸ projected

end Airbender.Delegation.Proofs
