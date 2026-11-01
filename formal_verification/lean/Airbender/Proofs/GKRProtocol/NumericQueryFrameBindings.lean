import Airbender.Proofs.GKRProtocol.NumericQueryFrameChecks

namespace Airbender.Compiler.NumericQueryFrameChecks
set_option warningAsError true

/-- Build a bounded source window without constructing the complete source list. -/
def window (values : Fin n → α) (first count : Nat) (bounded : first + count ≤ n) : List α :=
  List.ofFn fun index : Fin count => values ⟨first + index.val, by omega⟩

theorem window_binding (values : Fin n → α) (first count : Nat) (bounded : first + count ≤ n) :
    window values first count bounded = ((List.ofFn values).drop first).take count := by
  apply List.ext_getElem
  · simp only [window, List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro index left right
    simp only [window, List.getElem_ofFn, List.getElem_take, List.getElem_drop]

theorem map_window (values : List α) (encode : α → β) (first count : Nat) :
    ((values.drop first).take count).map encode = ((values.map encode).drop first).take count := by
  simp only [List.map_drop, List.map_take]

theorem slice_append (values : List α) (first left right : Nat) :
    (values.drop first).take (left + right) =
      (values.drop first).take left ++ (values.drop (first + left)).take right := by
  rw [List.take_add]
  simp only [List.drop_drop]

theorem merge_bindings (values source : List α) (first left right : Nat)
    (firstBinding : (values.drop first).take left = (source.drop first).take left)
    (secondBinding : (values.drop (first + left)).take right =
      (source.drop (first + left)).take right) :
    (values.drop first).take (left + right) = (source.drop first).take (left + right) := by
  rw [slice_append, slice_append, firstBinding, secondBinding]

theorem complete_binding (values source : List α) (count : Nat)
    (valuesLength : values.length = count) (sourceLength : source.length = count)
    (binding : (values.drop 0).take count = (source.drop 0).take count) : values = source := by
  have valueTake : values.take count = values := by rw [← valuesLength, List.take_length]
  have sourceTake : source.take count = source := by rw [← sourceLength, List.take_length]
  simpa only [List.drop_zero, valueTake, sourceTake] using binding

end Airbender.Compiler.NumericQueryFrameChecks
