import Airbender.Review.AddSub.Artifact
import Airbender.Review.Properties
import Airbender.Review.Field
import Airbender.Review.AddSub.Modular
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Constraints

namespace Airbender.AddSub.Proofs
open Airbender.Arithmetic

/-- The shared comparison equations force a canonical BabyBear result on every
    modular branch. No operand bounds or arithmetic-result premise is used. -/
theorem modular_canonical_output {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (s10 : w 10 = 0) (s11 : w 11 = 0) (s12 : w 12 = 0)
    (selected : w 13 + w 14 + w 15 + w 16 = 1) :
    (w 33).val + 65536 * (w 34).val < babyBearModulus := by
  have borrow := Verification.assertion_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.constraints]⟩
  have low := Verification.assertion_of_holds h
    ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have carry := Verification.assertion_of_holds h
    ⟨25, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, s10, s11, s12, selected] at borrow low high carry
  have b : w 40 = 1 := by linear_combination -borrow
  have boolean : w 39 * (w 39 - 1) = 0 := by
    simpa [mul_eq_zero, sub_eq_add_neg] using carry
  obtain ⟨c, cb, hc⟩ := boolean_nat boolean
  have rlo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have rhi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have olo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have ohi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at rlo rhi olo ohi
  have lowEq : (((w 37).val : Nat) : ZMod p) + 1 =
      (w 33).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc] at low
    linear_combination low
  have highEq : (c : ZMod p) + (w 38).val + 30720 = (w 34).val + 65536 := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc, b] at high
    linear_combination high
  exact Word.lt_of_borrow (output := ⟨(w 33).val, (w 34).val⟩)
    (remainder := ⟨(w 37).val, (w 38).val⟩) (modulus := ⟨1, 30720⟩)
    hp ⟨olo, ohi⟩ ⟨by decide, by decide⟩ ⟨rlo, rhi⟩ cb
    (by simpa using lowEq) (by simpa using highEq)

/-- All four custom arithmetic cases reuse the same canonical-output proof and
    shared soundness property. The fixed BabyBear artifact supplies Montgomery R^-1. -/
theorem modular_soundness :
    Modular.circuitModel.SoundnessUnder Modular.InterfaceAssumptions Modular.spec := by
  rintro input output w ⟨interfaces, constraints, mapping⟩
  have s10 := interfaces.selection 10 (by omega) (by omega)
  have s11 := interfaces.selection 11 (by omega) (by omega)
  have s12 := interfaces.selection 12 (by omega) (by omega)
  have s13 := interfaces.selection 13 (by omega) (by omega)
  have s14 := interfaces.selection 14 (by omega) (by omega)
  have s15 := interfaces.selection 15 (by omega) (by omega)
  have s16 := interfaces.selection 16 (by omega) (by omega)
  have nonstandard : w 10 = 0 ∧ w 11 = 0 ∧ w 12 = 0 := by
    cases hop : input.opcode <;> simp [hop, Modular.Opcode.selector] at s10 s11 s12
    all_goals exact ⟨s10, s11, s12⟩
  have selected : w 13 + w 14 + w 15 + w 16 = 1 := by
    cases hop : input.opcode <;>
      simp [hop, Modular.Opcode.selector] at s13 s14 s15 s16
    all_goals simp [s13, s14, s15, s16]
  have canonical : output.value < babyBearModulus := by
    simpa [Word.value, limbBase, mapping.outputLo, mapping.outputHi] using
      modular_canonical_output (by decide) constraints nonstandard.1 nonstandard.2.1
        nonstandard.2.2 selected
  have outputCast : (output.value : ZMod babyBearModulus) = w 33 + 65536 * w 34 := by
    simp [Word.value, limbBase, mapping.outputLo, mapping.outputHi]
  have intermediate := Verification.assertion_of_holds constraints
    ⟨1, by simp [importedConstraints, FlatOperation.constraints]⟩
  have result := Verification.assertion_of_holds constraints
    ⟨2, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mapping.left, mapping.right] at intermediate result
  have inverse : (943718400 : ZMod babyBearModulus) = (4294967296 : ZMod babyBearModulus)⁻¹ := by
    have unit : (943718400 : ZMod babyBearModulus) * 4294967296 = 1 := by decide
    have nonzero : (4294967296 : ZMod babyBearModulus) ≠ 0 := by decide
    calc
      (943718400 : ZMod babyBearModulus) =
          943718400 * (4294967296 * (4294967296 : ZMod babyBearModulus)⁻¹) := by
        rw [mul_inv_cancel₀ nonzero, mul_one]
      _ = _ := by rw [← mul_assoc, unit, one_mul]
  unfold Modular.spec
  rw [← ZMod.val_natCast_of_lt canonical]
  apply congrArg ZMod.val
  rw [outputCast]
  cases hop : input.opcode <;>
    simp [hop, Modular.Opcode.selector] at s13 s14 s15 s16 ⊢
  · simp [s13, s14, s15, s16] at result
    linear_combination result + mapping.right
  · simp [s13, s14, s15, s16] at result
    linear_combination result
  · simp [s13, s14, s15, s16] at result intermediate
    rw [← inverse]
    linear_combination result - intermediate
  · simp [s13, s14, s15, s16, mapping.oldDestination hop] at result intermediate
    rw [← inverse]
    linear_combination result - intermediate

end Airbender.AddSub.Proofs
