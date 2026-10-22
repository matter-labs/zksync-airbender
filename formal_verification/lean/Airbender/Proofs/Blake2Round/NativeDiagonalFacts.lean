import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2Round.NativeXorTransfer
import Airbender.Proofs.Blake2G.QueryCarries

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- All four addition carries are supplied by native carry-aware memberships. -/
theorem native_diagonal_addition_carries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 4) :
    (diagonalFrame call w).addCarries[slot].val < 3 := by
  have source := Verification.lookup_of_holds h
    ⟨NativeLayout.queryIndex .diagonal call NativeLayout.additionCarryQueries[slot], by
      rw [lookup_count]; have := call.isLt
      have := NativeLayout.additionCarryQueries[slot].isLt
      dsimp [NativeLayout.queryIndex]; omega⟩
  fin_cases call <;> fin_cases slot
  all_goals have bound := carry_value_bound hp 0 source (by norm_num [carryTags, Expression.eval])
  all_goals simpa [diagonalFrame, NativeLayout.Layout.read, NativeLayout.Location.read,
    NativeLayout.diagonal, NativeLayout.queryColumn, NativeLayout.queryIndex,
    importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment] using bound

/-- The first two C-addition carry flags remain native Boolean assertions. -/
theorem native_diagonal_first_c_flags {p : Nat} [Fact p.Prime]
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 2) :
    (diagonalFrame call w).cCarries[(slot.castLE (by decide) : Fin 4)] = 0 ∨
      (diagonalFrame call w).cCarries[(slot.castLE (by decide) : Fin 4)] = 1 := by
  have asserted := Verification.assertion_of_holds h
    ⟨NativeLayout.diagonalBooleanAssertion call slot, by
      rw [constraint_count]; have := call.isLt; have := slot.isLt
      dsimp [NativeLayout.diagonalBooleanAssertion]; omega⟩
  fin_cases call <;> fin_cases slot
  all_goals simpa [NativeLayout.diagonalBooleanAssertion, diagonalFrame,
    NativeLayout.Layout.read, NativeLayout.Location.read, NativeLayout.diagonal,
    importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using asserted

/-- The two final carry values are bounded by the native seven-bit carry table. -/
theorem native_diagonal_last_c_bounds {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 2) :
    (diagonalFrame call w).cCarries[(⟨2 + slot.val, by omega⟩ : Fin 4)].val < 3 := by
  have source := Verification.lookup_of_holds h
    ⟨NativeLayout.queryIndex .diagonal call NativeLayout.finalCarryQueries[slot], by
      rw [lookup_count]; have := call.isLt; have := NativeLayout.finalCarryQueries[slot].isLt
      dsimp [NativeLayout.queryIndex]; omega⟩
  fin_cases call <;> fin_cases slot
  all_goals have bound := carry_value_bound hp 1 source (by norm_num [carryTags, Expression.eval])
  all_goals simpa [diagonalFrame, NativeLayout.Layout.read, NativeLayout.Location.read,
    NativeLayout.diagonal, NativeLayout.queryColumn, NativeLayout.queryIndex,
    importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment] using bound

/-- Derive all flags from native acceptance and projected lookups. The shared
    G lemma derives the final two Boolean flags from bounded arithmetic. -/
theorem native_diagonal_flags_complete {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 262144)
    (compatible : SerializedInverse.Scale64 p) (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (queries : Blake2G.Proofs.QueryHolds (Blake2G.setupTable (fun _ => Vector.replicate 7 0))
      (diagonalFrame call w).assignment) :
    ∀ k : Fin 12,
      (diagonalFrame call w).base Blake2G.Variables.booleanColumns[1 + k.val] = 0 ∨
      (diagonalFrame call w).base Blake2G.Variables.booleanColumns[1 + k.val] = 1 :=
  (diagonalFrame call w).flags_from_queries hp compatible _ queries
    (native_diagonal_addition_carries (by omega) call h)
    (native_diagonal_first_c_flags call h)
    (native_diagonal_last_c_bounds (by omega) call h)

end Airbender.Blake2Round.Proofs
