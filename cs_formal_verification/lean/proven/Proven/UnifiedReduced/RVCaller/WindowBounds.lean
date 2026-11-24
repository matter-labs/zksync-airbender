module
public import Human.Trace.UnifiedReduced.PreparedHashWindows
public import Human.Trace.UnifiedReduced.MixedWindows

@[expose] public section
namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic

theorem ordered_hash_window_bounds {windows : List HashWindow} {cut : Nat}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval)) :
    (∀ window ∈ windows, cut ≤ window.lower ∧ window.lower ≤ window.upper ∧
      window.lower % 4 = 0 ∧ window.upper % 4 = 0) ∧
    windows.Pairwise (fun first second => first.upper ≤ second.lower) := by
  induction windows generalizing cut with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨lower, extent, first, last, rest⟩ := ordered
    obtain ⟨bounds, separated⟩ := ih rest
    constructor
    · intro window member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨lower, extent, first, last⟩
      · obtain ⟨after, extent', first', last'⟩ := bounds window member
        exact ⟨by omega, extent', first', last'⟩
    · exact List.pairwise_cons.mpr ⟨fun window member => (bounds window member).1, separated⟩

theorem ordered_hash_window_unique {windows : List HashWindow} {cut time : Nat}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    {first second : HashWindow} (one : first ∈ windows) (two : second ∈ windows)
    (firstRange : first.lower < time ∧ time ≤ first.upper)
    (secondRange : second.lower < time ∧ time ≤ second.upper) : first = second := by
  induction windows generalizing cut with
  | nil => cases one
  | cons head tail ih =>
    obtain ⟨_, _, _, _, rest⟩ := ordered
    have bounds := (ordered_hash_window_bounds rest).1
    rcases List.mem_cons.mp one with firstHead | firstTail
    · rcases List.mem_cons.mp two with secondHead | secondTail
      · exact firstHead.trans secondHead.symm
      · rw [firstHead] at firstRange
        have := (bounds second secondTail).1
        omega
    · rcases List.mem_cons.mp two with secondHead | secondTail
      · rw [secondHead] at secondRange
        have := (bounds first firstTail).1
        omega
      · exact ih rest firstTail secondTail

open Classical in
theorem disjoint_filter_flatMap_count {α β : Type} [BEq α] [LawfulBEq α] (rows : List α) (windows : List β)
    (select : β → α → Bool)
    (separated : windows.Pairwise (fun first second => ∀ row,
      ¬ (select first row = true ∧ select second row = true))) (row : α) :
    (windows.flatMap fun window => rows.filter (select window)).count row =
      if ∃ window ∈ windows, select window row = true then rows.count row else 0 := by
  classical
  induction windows with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨disjoint, rest⟩ := List.pairwise_cons.mp separated
    rw [List.flatMap_cons, List.count_append, ih rest]
    by_cases chosen : select head row = true
    · have absent : ¬ ∃ window ∈ tail, select window row = true := by
        rintro ⟨window, member, selected⟩
        exact disjoint window member row ⟨chosen, selected⟩
      rw [List.count_filter chosen]
      simp [chosen, absent]
    · have zero : (rows.filter (select head)).count row = 0 := by
        apply List.count_eq_zero.mpr
        simp [chosen]
      rw [zero]
      simp [chosen]

end Airbender.UnifiedReduced.Caller.Proofs
