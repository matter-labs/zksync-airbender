import Airbender.Review.Circuits.ReducedMachine.Row
import Airbender.Proofs.ReducedMachine.NativeArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.FinCases

namespace Airbender.ReducedMachine.NativeSelectorProofs
open Verification Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All eighteen mask bits are Boolean in the actual compiled constraints. -/
theorem bit_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (slot : Fin 18) : (w (17 + slot.val)).val ≤ 1 := by
  have bit := assertion_of_holds holds ⟨slot.val,by change slot.val < 117; omega⟩
  fin_cases slot
  all_goals
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at bit ⊢
    obtain ⟨n,bound,same⟩ := Arithmetic.boolean_nat (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

/-- Exact natural packed-mask equality; no field rollover can hide extra bits. -/
theorem packed {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    (w 17).val + 2 * (w 18).val + 4 * (w 19).val + 8 * (w 20).val + 16 * (w 21).val + 32 * (w 22).val + 64 * (w 23).val + 128 * (w 24).val + 256 * (w 25).val + 512 * (w 26).val + 1024 * (w 27).val + 2048 * (w 28).val + 4096 * (w 29).val + 8192 * (w 30).val + 16384 * (w 31).val + 32768 * (w 32).val + 65536 * (w 33).val + 131072 * (w 34).val = (w 12).val := by
  have b0 : (w 17).val ≤ 1 := bit_bounds holds ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := bit_bounds holds ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := bit_bounds holds ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := bit_bounds holds ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := bit_bounds holds ⟨4,by decide⟩
  have b5 : (w 22).val ≤ 1 := bit_bounds holds ⟨5,by decide⟩
  have b6 : (w 23).val ≤ 1 := bit_bounds holds ⟨6,by decide⟩
  have b7 : (w 24).val ≤ 1 := bit_bounds holds ⟨7,by decide⟩
  have b8 : (w 25).val ≤ 1 := bit_bounds holds ⟨8,by decide⟩
  have b9 : (w 26).val ≤ 1 := bit_bounds holds ⟨9,by decide⟩
  have b10 : (w 27).val ≤ 1 := bit_bounds holds ⟨10,by decide⟩
  have b11 : (w 28).val ≤ 1 := bit_bounds holds ⟨11,by decide⟩
  have b12 : (w 29).val ≤ 1 := bit_bounds holds ⟨12,by decide⟩
  have b13 : (w 30).val ≤ 1 := bit_bounds holds ⟨13,by decide⟩
  have b14 : (w 31).val ≤ 1 := bit_bounds holds ⟨14,by decide⟩
  have b15 : (w 32).val ≤ 1 := bit_bounds holds ⟨15,by decide⟩
  have b16 : (w 33).val ≤ 1 := bit_bounds holds ⟨16,by decide⟩
  have b17 : (w 34).val ≤ 1 := bit_bounds holds ⟨17,by decide⟩
  have equation := assertion_of_holds holds ⟨112,by change 112 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  apply Arithmetic.bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
    (by change _ < 2147483647; omega) (ZMod.val_lt _)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
  linear_combination equation

private theorem shift_bits_left {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool)
    (mask : w 12 = (ShiftMode.left.mask useRegister : ZMod mersenne31Modulus)) :
    w 18 = (if useRegister then 1 else 0) ∧
      ∀ slot : Fin 12, w (20 + slot.val) = (if slot.val = 9 then 1 else 0) := by
  have b0 : (w 17).val ≤ 1 := bit_bounds holds ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := bit_bounds holds ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := bit_bounds holds ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := bit_bounds holds ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := bit_bounds holds ⟨4,by decide⟩
  have b5 : (w 22).val ≤ 1 := bit_bounds holds ⟨5,by decide⟩
  have b6 : (w 23).val ≤ 1 := bit_bounds holds ⟨6,by decide⟩
  have b7 : (w 24).val ≤ 1 := bit_bounds holds ⟨7,by decide⟩
  have b8 : (w 25).val ≤ 1 := bit_bounds holds ⟨8,by decide⟩
  have b9 : (w 26).val ≤ 1 := bit_bounds holds ⟨9,by decide⟩
  have b10 : (w 27).val ≤ 1 := bit_bounds holds ⟨10,by decide⟩
  have b11 : (w 28).val ≤ 1 := bit_bounds holds ⟨11,by decide⟩
  have b12 : (w 29).val ≤ 1 := bit_bounds holds ⟨12,by decide⟩
  have b13 : (w 30).val ≤ 1 := bit_bounds holds ⟨13,by decide⟩
  have b14 : (w 31).val ≤ 1 := bit_bounds holds ⟨14,by decide⟩
  have b15 : (w 32).val ≤ 1 := bit_bounds holds ⟨15,by decide⟩
  have b16 : (w 33).val ≤ 1 := bit_bounds holds ⟨16,by decide⟩
  have b17 : (w 34).val ≤ 1 := bit_bounds holds ⟨17,by decide⟩
  have natural := packed holds
  have maskValue := congrArg ZMod.val mask
  have maskBound : ShiftMode.left.mask useRegister < mersenne31Modulus := by
    cases useRegister <;> decide
  rw [ZMod.val_natCast_of_lt maskBound] at maskValue
  rw [maskValue] at natural
  constructor
  · cases useRegister
    all_goals
      simp only [ShiftMode.mask,Bool.false_eq_true,if_false,if_true] at natural ⊢
      apply ZMod.val_injective mersenne31Modulus
      simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
      clear mask maskValue maskBound
      omega
  · intro slot
    fin_cases slot
    all_goals
      simp
      apply ZMod.val_injective mersenne31Modulus
      simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
      cases useRegister <;> simp only [ShiftMode.mask,if_true,if_false,Bool.false_eq_true] at natural <;> clear mask maskValue maskBound <;> omega


private theorem shift_bits_right {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool)
    (mask : w 12 = (ShiftMode.right.mask useRegister : ZMod mersenne31Modulus)) :
    w 18 = (if useRegister then 1 else 0) ∧
      ∀ slot : Fin 12, w (20 + slot.val) = (if slot.val = 9 then 1 else 0) := by
  have b0 : (w 17).val ≤ 1 := bit_bounds holds ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := bit_bounds holds ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := bit_bounds holds ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := bit_bounds holds ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := bit_bounds holds ⟨4,by decide⟩
  have b5 : (w 22).val ≤ 1 := bit_bounds holds ⟨5,by decide⟩
  have b6 : (w 23).val ≤ 1 := bit_bounds holds ⟨6,by decide⟩
  have b7 : (w 24).val ≤ 1 := bit_bounds holds ⟨7,by decide⟩
  have b8 : (w 25).val ≤ 1 := bit_bounds holds ⟨8,by decide⟩
  have b9 : (w 26).val ≤ 1 := bit_bounds holds ⟨9,by decide⟩
  have b10 : (w 27).val ≤ 1 := bit_bounds holds ⟨10,by decide⟩
  have b11 : (w 28).val ≤ 1 := bit_bounds holds ⟨11,by decide⟩
  have b12 : (w 29).val ≤ 1 := bit_bounds holds ⟨12,by decide⟩
  have b13 : (w 30).val ≤ 1 := bit_bounds holds ⟨13,by decide⟩
  have b14 : (w 31).val ≤ 1 := bit_bounds holds ⟨14,by decide⟩
  have b15 : (w 32).val ≤ 1 := bit_bounds holds ⟨15,by decide⟩
  have b16 : (w 33).val ≤ 1 := bit_bounds holds ⟨16,by decide⟩
  have b17 : (w 34).val ≤ 1 := bit_bounds holds ⟨17,by decide⟩
  have natural := packed holds
  have maskValue := congrArg ZMod.val mask
  have maskBound : ShiftMode.right.mask useRegister < mersenne31Modulus := by
    cases useRegister <;> decide
  rw [ZMod.val_natCast_of_lt maskBound] at maskValue
  rw [maskValue] at natural
  constructor
  · cases useRegister
    all_goals
      simp only [ShiftMode.mask,Bool.false_eq_true,if_false,if_true] at natural ⊢
      apply ZMod.val_injective mersenne31Modulus
      simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
      clear mask maskValue maskBound
      omega
  · intro slot
    fin_cases slot
    all_goals
      simp
      apply ZMod.val_injective mersenne31Modulus
      simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
      cases useRegister <;> simp only [ShiftMode.mask,if_true,if_false,Bool.false_eq_true] at natural <;> clear mask maskValue maskBound <;> omega


private theorem shift_bits_arithmetic {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool)
    (mask : w 12 = (ShiftMode.arithmetic.mask useRegister : ZMod mersenne31Modulus)) :
    w 18 = (if useRegister then 1 else 0) ∧
      ∀ slot : Fin 12, w (20 + slot.val) = (if slot.val = 9 then 1 else 0) := by
  have b0 : (w 17).val ≤ 1 := bit_bounds holds ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := bit_bounds holds ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := bit_bounds holds ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := bit_bounds holds ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := bit_bounds holds ⟨4,by decide⟩
  have b5 : (w 22).val ≤ 1 := bit_bounds holds ⟨5,by decide⟩
  have b6 : (w 23).val ≤ 1 := bit_bounds holds ⟨6,by decide⟩
  have b7 : (w 24).val ≤ 1 := bit_bounds holds ⟨7,by decide⟩
  have b8 : (w 25).val ≤ 1 := bit_bounds holds ⟨8,by decide⟩
  have b9 : (w 26).val ≤ 1 := bit_bounds holds ⟨9,by decide⟩
  have b10 : (w 27).val ≤ 1 := bit_bounds holds ⟨10,by decide⟩
  have b11 : (w 28).val ≤ 1 := bit_bounds holds ⟨11,by decide⟩
  have b12 : (w 29).val ≤ 1 := bit_bounds holds ⟨12,by decide⟩
  have b13 : (w 30).val ≤ 1 := bit_bounds holds ⟨13,by decide⟩
  have b14 : (w 31).val ≤ 1 := bit_bounds holds ⟨14,by decide⟩
  have b15 : (w 32).val ≤ 1 := bit_bounds holds ⟨15,by decide⟩
  have b16 : (w 33).val ≤ 1 := bit_bounds holds ⟨16,by decide⟩
  have b17 : (w 34).val ≤ 1 := bit_bounds holds ⟨17,by decide⟩
  have natural := packed holds
  have maskValue := congrArg ZMod.val mask
  have maskBound : ShiftMode.arithmetic.mask useRegister < mersenne31Modulus := by
    cases useRegister <;> decide
  rw [ZMod.val_natCast_of_lt maskBound] at maskValue
  rw [maskValue] at natural
  constructor
  · cases useRegister
    all_goals
      simp only [ShiftMode.mask,Bool.false_eq_true,if_false,if_true] at natural ⊢
      apply ZMod.val_injective mersenne31Modulus
      simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
      clear mask maskValue maskBound
      omega
  · intro slot
    fin_cases slot
    all_goals
      simp
      apply ZMod.val_injective mersenne31Modulus
      simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
      cases useRegister <;> simp only [ShiftMode.mask,if_true,if_false,Bool.false_eq_true] at natural <;> clear mask maskValue maskBound <;> omega


/-- A decoded shift mask determines all shared operation flags and rs2 routing.
    Individual selector values are conclusions, never interface premises. -/
theorem shift_bits {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    w 18 = (if useRegister then 1 else 0) ∧
      ∀ slot : Fin 12, w (20 + slot.val) = (if slot.val = 9 then 1 else 0) := by
  cases mode with
  | left => exact shift_bits_left holds useRegister mask
  | right => exact shift_bits_right holds useRegister mask
  | arithmetic => exact shift_bits_arithmetic holds useRegister mask

end Airbender.ReducedMachine.NativeSelectorProofs
