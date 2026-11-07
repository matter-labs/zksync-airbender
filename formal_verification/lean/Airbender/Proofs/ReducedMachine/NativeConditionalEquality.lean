import Airbender.Proofs.ReducedMachine.NativeComparisonResult

namespace Airbender.ReducedMachine.NativeConditionalEqualityProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact zero-test semantics for the actual shared subtraction remainder. The
    active conditional major flag must be derived by the operation's decoder.
    Scalar range checks suffice; no source-word bounds or zero answer is given. -/
theorem remainder_zero {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (active : w 23 = 1) :
    w 68 = if (w 61).val = 0 ∧ (w 62).val = 0 then 1 else 0 := by
  have e78 := assertion_of_holds holds ⟨78,by change 78 < 117; decide⟩
  have e79 := assertion_of_holds holds ⟨79,by change 79 < 117; decide⟩
  have e80 := assertion_of_holds holds ⟨80,by change 80 < 117; decide⟩
  have e81 := assertion_of_holds holds ⟨81,by change 81 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,active] at e78 e79 e80 e81
  have low : w 97 = w 61 := by linear_combination -e78
  have high : w 98 = w 62 := by linear_combination -e79
  rw [low,high] at e80 e81
  have ranges := NativeArithmeticResultProofs.scalar_bounds holds
  by_cases zero : (w 61).val = 0 ∧ (w 62).val = 0
  · have zl : w 61 = 0 := by apply ZMod.val_injective mersenne31Modulus; simpa using zero.1
    have zh : w 62 = 0 := by apply ZMod.val_injective mersenne31Modulus; simpa using zero.2
    simp only [if_pos zero]
    rw [zl,zh] at e80
    linear_combination e80
  · simp only [if_neg zero]
    have sumBound : (w 61).val + (w 62).val < mersenne31Modulus := by
      change (w 61).val < 65536 ∧ (w 62).val < 65536 at ranges
      change _ < 2147483647
      omega
    have notSum : w 61 + w 62 ≠ 0 := by
      intro sum
      have natural : (w 61).val + (w 62).val = 0 := by
        have cast : (((w 61).val + (w 62).val : Nat) : ZMod mersenne31Modulus) = 0 := by
          simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using sum
        have value := congrArg ZMod.val cast
        simpa only [ZMod.val_natCast_of_lt sumBound,ZMod.val_zero] using value
      exact zero (by omega)
    have product : w 68 * (w 61 + w 62) = 0 := by linear_combination e81
    exact (mul_eq_zero.mp product).resolve_right notSum

end Airbender.ReducedMachine.NativeConditionalEqualityProofs
