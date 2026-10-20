import Human.Helpers.Core.ExternalStream
import Slop.Trace.RowHistory

namespace Airbender.Trace.ExternalStream.Proofs

variable {Row : Type} (read : Row → Bool) (response : Row → BitVec 32)

private theorem consumed_cons (row : Row) (rest : List Row) :
    ExternalStream.consumed read response (row :: rest) = ExternalStream.consumed read response rest ++
      (if read row then [response row] else []) := by
  cases selected : read row <;> simp [ExternalStream.consumed, List.filterMap_append, selected]

theorem consumed_length (rows : List Row) :
    (ExternalStream.consumed read response rows).length = (rows.filter read).length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [consumed_cons]
    simp only [List.length_append, List.filter_cons]
    by_cases selected : read row = true
    · simp [selected, ih]
    · simp [selected, ih]

theorem ordered_consumption (clock : Row → Nat) {rows : List Row} {stream : List (BitVec 32)}
    (ordered : rows.Pairwise (fun a b => clock b < clock a))
    (ports : ∀ row ∈ rows, read row = true →
      stream[(rows.filter fun earlier => read earlier &&
        decide (clock earlier < clock row)).length]? = some (response row)) :
    ∃ rest, stream = ExternalStream.consumed read response rows ++ rest := by
  induction rows with
  | nil => exact ⟨stream, rfl⟩
  | cons row rows ih =>
    obtain ⟨earlier, ordered⟩ := List.pairwise_cons.mp ordered
    have remaining : ∀ old ∈ rows, read old = true →
        stream[(rows.filter fun previous => read previous &&
          decide (clock previous < clock old)).length]? = some (response old) := by
      intro old member selected
      have bound := earlier old member
      have supplied := ports old (List.mem_cons_of_mem row member) selected
      simpa [List.filter_cons, Nat.not_lt.mpr (Nat.le_of_lt bound)] using supplied
    obtain ⟨rest, suffix⟩ := ih ordered remaining
    by_cases selected : read row = true
    · have index : (rows.filter fun old => read old &&
          decide (clock old < clock row)).length = (ExternalStream.consumed read response rows).length := by
        rw [consumed_length]
        congr 1
        apply List.filter_congr
        intro old member
        simp [earlier old member]
      have supplied := ports row List.mem_cons_self selected
      simp only [List.filter_cons, lt_self_iff_false, decide_false,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte] at supplied
      rw [index, suffix, List.getElem?_append_right (by omega), Nat.sub_self] at supplied
      cases rest with
      | nil => simp at supplied
      | cons value rest =>
        have valueEq : value = response row := by simpa using supplied
        subst value
        exact ⟨rest, by simpa [consumed_cons, selected, List.append_assoc] using suffix⟩
    · exact ⟨rest, by simpa [consumed_cons, selected] using suffix⟩

variable {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] [Trace.Proofs.ClockLaws Kind p]

theorem native_consumption (read : Trace.Row p Kind → Bool)
    (response : Trace.Row p Kind → BitVec 32) (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : Ports Trace.Row.clock read response trace.rows stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, stream = ExternalStream.consumed read response rows ++ rest := by
  obtain ⟨rows, permutation, ordered, _, _⟩ :=
    Trace.Proofs.native_row_order hp inverse accepted boundary
  refine ⟨rows, permutation, ordered, ordered_consumption read response Trace.Row.clock ordered ?_⟩
  intro row member selected
  have supplied := ports row (permutation.mem_iff.mp member) selected
  have indexEq := (permutation.filter (fun earlier => read earlier &&
    decide (earlier.clock < row.clock))).length_eq
  simpa only [ExternalStream.index, ← indexEq] using supplied

end Airbender.Trace.ExternalStream.Proofs
