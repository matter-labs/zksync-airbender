module
public import Human.Compiler.LookupArgument
public import Mathlib.Data.List.Basic
@[expose] public section
namespace Airbender.Compiler.LookupArgument
/-- Per-query membership gives exact tuple matching with one selected occurrence per request. -/
noncomputable def of_membership {Index Value : Type} (table : Index → Value) (requests : List Value)
    (membership : ∀ value ∈ requests, ∃ index, value = table index) : LookupArgument table requests where
  rows := requests.attach.map fun value => Classical.choose (membership value.val value.property)
  multiplicity := fun _ => 1
  balance := by
    have singletonMap (rows : List Index) : rows.flatMap (fun index => [table index]) = rows.map table := by
      induction rows with
      | nil => rfl
      | cons first rest ih => exact congrArg (table first :: ·) ih
    simp only [List.replicate_one]
    rw [singletonMap, List.map_map]
    apply List.Perm.of_eq
    symm
    calc
      _ = requests.attach.map Subtype.val := by
        apply List.map_congr_left
        intro value _
        exact (Classical.choose_spec (membership value.val value.property)).symm
      _ = requests := by simpa only [List.map_id, id_eq] using (List.attach_map_val (l := requests) (f := id))
end Airbender.Compiler.LookupArgument
