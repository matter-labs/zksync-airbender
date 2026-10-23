import Airbender.Proofs.Blake2Round.NativeDiagonalCarryBounds
import Airbender.Proofs.Blake2Round.NativeBooleanBindings
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
  exact NativeDiagonalCarryBounds.addition_bound hp call slot source

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
  rw [NativeBooleanBindings.diagonal_expression (p := p)] at asserted
  rw [NativeBooleanBindings.diagonal_first_c_read (p := p) call slot w]
  simpa only [Verification.environment] using
    (Arithmetic.nativeBooleanExpression_eq_zero (p := p)
      (426 + 30 * call.val + 3 * slot.val) (Verification.environment w)).mp asserted

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
  exact NativeDiagonalCarryBounds.final_c_bound hp call slot source

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
