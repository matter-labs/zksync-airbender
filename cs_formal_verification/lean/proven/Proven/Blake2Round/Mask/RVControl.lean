module
public import Proven.Blake2Round.Mask.Native
public import Proven.Arithmetic.Digits

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
set_option warningAsError true
open Arithmetic
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem control_digit_index : ∀ i : Fin 13, Variables.controlBits[i] = 139 + i.val := by
  decide

/-- The thirteen native high-word control digits. -/
def controlValue (w : Nat → ZMod babyBearModulus) : Nat :=
  ∑ i : Fin 13, 2 ^ i.val * (w (139 + i.val)).val

/-- The native Boolean control digits are canonical binary digits. -/
theorem control_digit_bounds {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    ∀ i : Fin 13, (w (139 + i.val)).val < 2 := by
  intro i
  have bit := Control.Proofs.control_bits holds i
  rw [control_digit_index] at bit
  have bound := Arithmetic.boolean_val bit
  omega

/-- The imported control equation binds the complete high-word bit decomposition. -/
theorem control_high_value {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    (w 136).val = controlValue w := by
  have bound : controlValue w < 8192 := by
    exact weighted_limb_bound (by decide) (control_digit_bounds holds)
  have equation := Verification.assertion_of_holds holds ⟨1, by rw [constraint_count]; decide⟩
  op_index at equation
  simp [Expression.eval, Verification.environment] at equation
  have field : ((controlValue w : Nat) : ZMod babyBearModulus) = w 136 := by
    simp only [controlValue, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Nat.reduceAdd, Nat.reducePow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
      ZMod.natCast_zmod_val]
    linear_combination equation
  have values := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)] at values
  exact values.symm

/-- A weighted sum of thirteen binary digits retains each digit. -/
theorem thirteen_digits (digits : Fin 13 → Nat) (bounded : ∀ i, digits i < 2) (i : Fin 13) :
    (∑ j : Fin 13, 2 ^ j.val * digits j) / 2 ^ i.val % 2 = digits i := by
  have b0 := bounded 0
  have b1 := bounded 1
  have b2 := bounded 2
  have b3 := bounded 3
  have b4 := bounded 4
  have b5 := bounded 5
  have b6 := bounded 6
  have b7 := bounded 7
  have b8 := bounded 8
  have b9 := bounded 9
  have b10 := bounded 10
  have b11 := bounded 11
  have b12 := bounded 12
  fin_cases i
  all_goals norm_num [Fin.sum_univ_succ] at *
  all_goals omega

/-- The RV control bits equal the native Boolean digits read from the high word. -/
theorem native_control_bit {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (bounded : (inputOf w).controller.Bounded) (i : Fin 13) :
    (inputOf w).controller.toBitVec.getLsbD (16 + i.val) = decide (w (139 + i.val) = 1) := by
  have word : (inputOf w).controller = ⟨(w 135).val, (w 136).val⟩ := control_read w
  have low : (w 135).val < 65536 := by simpa only [word, Word.Bounded, limbBase] using bounded.1
  have quotient : (inputOf w).controller.toBitVec.toNat / 65536 = (w 136).val := by
    rw [Word.toBitVec_toNat bounded, word]
    change ((w 135).val + 65536 * (w 136).val) / 65536 = (w 136).val
    omega
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, pow_add,
    show 2 ^ 16 = 65536 from rfl, ← Nat.div_div_eq_div_mul, quotient, control_high_value holds]
  have digit := thirteen_digits (fun i => (w (139 + i.val)).val) (control_digit_bounds holds) i
  change controlValue w / 2 ^ i.val % 2 = (w (139 + i.val)).val at digit
  rw [digit]
  have bit := Control.Proofs.control_bits holds i
  rw [control_digit_index] at bit
  rcases bit with zero | one
  · simp [zero]
  · rw [one]
    decide

end Airbender.Blake2Round.Mask.Proofs
