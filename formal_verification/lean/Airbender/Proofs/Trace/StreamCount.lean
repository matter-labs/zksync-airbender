import Airbender.Proofs.Trace.ExternalStream

namespace Airbender.Trace.ExternalStream.Proofs
set_option warningAsError true

theorem count_at_row {Row : Type} (clock : Row → Nat) (read : Row → Bool)
    (rows : List Row) (row : Row) :
    countBefore clock read rows (clock row) = ExternalStream.index clock read rows row := rfl

/-- Four-aligned, distinct native clocks isolate one instruction's read. -/
theorem count_after_cycle {Row : Type} (clock : Row → Nat) (read : Row → Bool)
    {rows : List Row} {row : Row} (member : row ∈ rows)
    (distinct : (rows.map clock).Nodup)
    (aligned : ∀ item ∈ rows, clock item % 4 = 0) :
    countBefore clock read rows (clock row + 4) =
      countBefore clock read rows (clock row) + (if read row then 1 else 0) := by
  induction rows with
  | nil => simp at member
  | cons first rest ih =>
    have unique := List.nodup_cons.mp distinct
    have restAligned : ∀ item ∈ rest, clock item % 4 = 0 :=
      fun item included => aligned item (List.mem_cons_of_mem _ included)
    rcases List.mem_cons.mp member with same | included
    · subst first
      have predicates : rest.filter (fun old => read old && decide (clock old < clock row + 4)) =
          rest.filter (fun old => read old && decide (clock old < clock row)) := by
        apply List.filter_congr
        intro old present
        have different : clock old ≠ clock row := by
          intro equal
          exact unique.1 (List.mem_map.mpr ⟨old, present, equal⟩)
        have oldAligned := restAligned old present
        have rowAligned := aligned row List.mem_cons_self
        have same : (clock old < clock row + 4) ↔ clock old < clock row := by omega
        simp only [same]
      have advance : clock row < clock row + 4 := by omega
      cases selected : read row <;>
        simp [countBefore, advance, selected, predicates, Nat.add_comm]
    · have different : clock first ≠ clock row := by
        intro equal
        exact unique.1 (List.mem_map.mpr ⟨row, included, equal.symm⟩)
      have firstAligned := aligned first List.mem_cons_self
      have rowAligned := restAligned row included
      have same : (clock first < clock row + 4) ↔ clock first < clock row := by omega
      have tail := ih included unique.2 restAligned
      unfold countBefore at tail ⊢
      simp only [List.filter_cons, same]
      split_ifs <;> simp_all

theorem count_at_start {Row : Type} (clock : Row → Nat) (read : Row → Bool)
    (rows : List Row) (boundary : Nat)
    (lower : ∀ row ∈ rows, boundary ≤ clock row) :
    countBefore clock read rows boundary = 0 := by
  unfold countBefore
  rw [List.filter_eq_nil_iff.mpr ?_]
  · rfl
  · intro row member
    simp [Nat.not_lt.mpr (lower row member)]

theorem count_at_finish {Row : Type} (clock : Row → Nat) (read : Row → Bool)
    (rows : List Row) (boundary : Nat)
    (upper : ∀ row ∈ rows, clock row < boundary) :
    countBefore clock read rows boundary = ExternalStream.count read rows := by
  unfold countBefore ExternalStream.count
  congr 1
  apply List.filter_congr
  intro row member
  simp [upper row member]

end Airbender.Trace.ExternalStream.Proofs
