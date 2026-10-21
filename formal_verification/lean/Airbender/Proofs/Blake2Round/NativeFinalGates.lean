import Airbender.Proofs.Blake2Round.NativeFinalLayout
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The native final selector is the Boolean OR expression of the two admitted
    final-round conditions. Round-mask interpretation is handled separately. -/
theorem native_final_flag {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    w 152 = w 148 * w 139 - w 148 * w 151 + w 151 := by
  have flag := Verification.assertion_of_holds h
    ⟨NativeFinalLayout.flagAssertion, by rw [constraint_count]; norm_num [NativeFinalLayout.flagAssertion]⟩
  simp [NativeFinalLayout.flagAssertion, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment] at flag
  linear_combination -flag

/-- One native state mux equation for either half of finalization. -/
theorem native_final_mux {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (limb : Fin 16) :
    NativeFinalLayout.stateWrite w limb = NativeFinalLayout.stateRead w limb + w 152 *
      (NativeFinalLayout.temporary w limb 4 +
        (if limb.val < 8 then 128 else 256) * NativeFinalLayout.temporary w limb 5 -
          NativeFinalLayout.stateRead w limb) := by
  have equation := Verification.assertion_of_holds h
    ⟨NativeFinalLayout.muxAssertion limb, by
      rw [constraint_count]; have := limb.isLt; dsimp [NativeFinalLayout.muxAssertion]; omega⟩
  fin_cases limb
  all_goals simp [NativeFinalLayout.muxAssertion, NativeFinalLayout.stateWrite,
    NativeFinalLayout.stateRead, NativeFinalLayout.temporary, importedConstraints,
    FlatOperation.constraints, Expression.eval, Verification.environment] at equation ⊢
  all_goals linear_combination -equation

/-- Active finalization selects the two actual output chunks. -/
theorem native_final_active_write {p : Nat} [Fact p.Prime] (limb : Fin 16) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (enabled : w 152 = 1) :
    NativeFinalLayout.stateWrite w limb = NativeFinalLayout.temporary w limb 4 +
      (if limb.val < 8 then 128 else 256) * NativeFinalLayout.temporary w limb 5 := by
  have equation := native_final_mux h limb
  rw [enabled] at equation
  linear_combination equation

end Airbender.Blake2Round.Proofs
