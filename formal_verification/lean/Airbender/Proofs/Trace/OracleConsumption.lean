import Airbender.Proofs.Trace.NonDeterminism
import Airbender.Proofs.Trace.RowHistory

namespace Airbender.Trace.NonDeterminism.Proofs
open Trace.Proofs

variable {p : Nat} [Fact p.Prime]

/-- A physical reordering cannot change the external-input position. -/
theorem read_index_permutation {first second : Data p}
    (permutation : first.rows.Perm second.rows) (row : Row p) :
    readIndex first row = readIndex second row :=
  (permutation.filter _).length_eq

private theorem consumed_cons (row : Row p) (rest : List (Row p)) :
    consumed (row :: rest) = consumed rest ++
      (if isRead row then [response row] else []) := by
  cases read : isRead row <;> simp [consumed, List.filterMap_append, read]

private theorem consumed_length (rows : List (Row p)) :
    (consumed rows).length = (rows.filter isRead).length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [consumed_cons]
    simp only [List.length_append, List.filter_cons]
    by_cases read : isRead row = true
    · simp [read, ih]
    · simp [read, ih]

/-- Sorted native rows consume exactly a prefix of an independent stream.
    No instruction execution or fixed-stream authentication is claimed here. -/
theorem ordered_consumption {rows : List (Row p)} {stream : List (BitVec 32)}
    (ordered : rows.Pairwise (fun a b => rowClock b < rowClock a))
    (ports : ∀ row ∈ rows, isRead row = true →
      stream[(rows.filter fun earlier => isRead earlier &&
        decide (rowClock earlier < rowClock row)).length]? = some (response row)) :
    ∃ rest, stream = consumed rows ++ rest := by
  induction rows with
  | nil => exact ⟨stream, rfl⟩
  | cons row rows ih =>
    obtain ⟨earlier, ordered⟩ := List.pairwise_cons.mp ordered
    have remaining : ∀ old ∈ rows, isRead old = true →
        stream[(rows.filter fun previous => isRead previous &&
          decide (rowClock previous < rowClock old)).length]? = some (response old) := by
      intro old member read
      have bound := earlier old member
      have supplied := ports old (List.mem_cons_of_mem row member) read
      simpa [List.filter_cons, Nat.not_lt.mpr (Nat.le_of_lt bound)] using supplied
    obtain ⟨rest, suffix⟩ := ih ordered remaining
    by_cases read : isRead row = true
    · have index : (rows.filter fun old => isRead old &&
          decide (rowClock old < rowClock row)).length = (consumed rows).length := by
        rw [consumed_length]
        congr 1
        apply List.filter_congr
        intro old member
        simp [earlier old member]
      have supplied := ports row List.mem_cons_self read
      simp only [List.filter_cons, lt_self_iff_false, decide_false,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte] at supplied
      rw [index, suffix, List.getElem?_append_right (by omega), Nat.sub_self] at supplied
      cases rest with
      | nil => simp at supplied
      | cons value rest =>
        have valueEq : value = response row := by simpa using supplied
        subst value
        exact ⟨rest, by simpa [consumed_cons, read, List.append_assoc] using suffix⟩
    · exact ⟨rest, by simpa [consumed_cons, read] using suffix⟩

/-- Imported clocks and logical matching derive the order. The stream boundary
    is then a chronological prefix, regardless of physical row storage order. -/
theorem native_consumption (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : StreamPorts trace stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => rowClock b < rowClock a) ∧
      ∃ rest, stream = consumed rows ++ rest := by
  obtain ⟨rows, permutation, ordered, _, _⟩ :=
    Trace.Proofs.native_row_order hp inverse accepted boundary
  refine ⟨rows, permutation, ordered, ordered_consumption ordered ?_⟩
  intro row member read
  have supplied := ports row (permutation.mem_iff.mp member) read
  change stream[readIndex { trace with rows := rows } row]? = _
  rw [read_index_permutation permutation]
  exact supplied

end Airbender.Trace.NonDeterminism.Proofs
