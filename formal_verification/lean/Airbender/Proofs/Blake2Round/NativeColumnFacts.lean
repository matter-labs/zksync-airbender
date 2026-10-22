import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2Round.NativeXorTransfer
import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

export NativeLayout (columnCarryColumns columnBooleanColumns)

/-- Actual carry-aware memberships bound each of the four native carries. -/
theorem native_column_carries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 4) :
    (w ((columnCarryColumns call)[slot])).val < 3 := by
  have source := Verification.lookup_of_holds holds
    ⟨NativeLayout.queryIndex .column call NativeLayout.additionCarryQueries[slot], by
      rw [lookup_count]
      have a := call.isLt
      have b := NativeLayout.additionCarryQueries[slot].isLt
      dsimp [NativeLayout.queryIndex]
      omega⟩
  fin_cases call <;> fin_cases slot
  all_goals have bound := carry_value_bound hp 0 source (by
    norm_num [carryTags, Expression.eval])
  all_goals simpa [columnCarryColumns, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment] using bound

/-- The four remaining carries are the native Boolean assertions. -/
theorem native_column_flags {p : Nat} [Fact p.Prime]
    (call : Fin 4) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 4) :
    w ((columnBooleanColumns call)[slot]) = 0 ∨ w ((columnBooleanColumns call)[slot]) = 1 := by
  have asserted := Verification.assertion_of_holds holds
    ⟨NativeLayout.columnBooleanAssertion call slot, by
      dsimp [NativeLayout.columnBooleanAssertion]
      rw [constraint_count]; have a := call.isLt; have b := slot.isLt; omega⟩
  fin_cases call <;> fin_cases slot
  all_goals simpa [NativeLayout.columnBooleanAssertion, columnBooleanColumns, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero]
    using asserted

end Airbender.Blake2Round.Proofs
