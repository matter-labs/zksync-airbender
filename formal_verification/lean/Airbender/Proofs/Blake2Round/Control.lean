import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Review.Circuits.Blake2Round.Control
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Round.Control.Proofs
open Arithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem control_bits {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 6)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 13, w Variables.controlBits[i] = 0 ∨ w Variables.controlBits[i] = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h ⟨124 + i.val,
    by rw [constraint_count]; have size := i.isLt; omega⟩
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, Variables.controlBits,
    mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
  all_goals exact flag

/-- Read/write control arithmetic uses only imported assertions. No exclusive
    round-mask, pointer, memory or XOR-table premise is needed. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 8192 ≤ p)
    (setup : Table (ZMod p) (fields 6)) :
    Properties.Soundness (circuitModel setup).relation spec := by
  intro input output w ⟨h, mapping⟩
  have bits (i : Fin 13) : (w Variables.controlBits[i]).val ≤ 1 :=
    boolean_val (control_bits h i)
  have b0 := bits ⟨0, by decide⟩
  have b1 := bits ⟨1, by decide⟩
  have b2 := bits ⟨2, by decide⟩
  have b3 := bits ⟨3, by decide⟩
  have b4 := bits ⟨4, by decide⟩
  have b5 := bits ⟨5, by decide⟩
  have b6 := bits ⟨6, by decide⟩
  have b7 := bits ⟨7, by decide⟩
  have b8 := bits ⟨8, by decide⟩
  have b9 := bits ⟨9, by decide⟩
  have b10 := bits ⟨10, by decide⟩
  have b11 := bits ⟨11, by decide⟩
  have b12 := bits ⟨12, by decide⟩
  change (w 139).val ≤ 1 at b0
  change (w 140).val ≤ 1 at b1
  change (w 141).val ≤ 1 at b2
  change (w 142).val ≤ 1 at b3
  change (w 143).val ≤ 1 at b4
  change (w 144).val ≤ 1 at b5
  change (w 145).val ≤ 1 at b6
  change (w 146).val ≤ 1 at b7
  change (w 147).val ≤ 1 at b8
  change (w 148).val ≤ 1 at b9
  change (w 149).val ≤ 1 at b10
  change (w 150).val ≤ 1 at b11
  change (w 151).val ≤ 1 at b12
  let controls := (w 139).val + 2 * (w 140).val + 4 * (w 141).val
  let rounds := (w 142).val + 2 * (w 143).val + 4 * (w 144).val +
    8 * (w 145).val + 16 * (w 146).val + 32 * (w 147).val +
    64 * (w 148).val + 128 * (w 149).val + 256 * (w 150).val
  have controlsBound : controls < 8 := by dsimp [controls]; omega
  have roundsBound : rounds < 512 := by dsimp [rounds]; omega
  have read := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨106, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨107, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at read low high
  have readField : ((controls + 8 * rounds + 4096 * (w 151).val : Nat) : ZMod p) = w 136 := by
    simp only [controls, rounds, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    linear_combination read
  have writeField : ((controls + 16 * rounds : Nat) : ZMod p) = w 138 := by
    simp only [controls, rounds, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    linear_combination high
  have readBound : controls + 8 * rounds + 4096 * (w 151).val < p := by omega
  have writeBound : controls + 16 * rounds < p := by omega
  have readValue : (w 136).val = controls + 8 * rounds + 4096 * (w 151).val := by
    rw [← readField]
    exact ZMod.val_natCast_of_lt readBound
  have writeValue : (w 138).val = controls + 16 * rounds := by
    rw [← writeField]
    exact ZMod.val_natCast_of_lt writeBound
  rw [mapping.inputWord, mapping.outputWord]
  refine ⟨?_, ?_⟩
  · change (w 136).val < 8192
    omega
  change ⟨(w 137).val, (w 138).val⟩ = next ⟨(w 135).val, (w 136).val⟩
  unfold next
  simp only [readValue, writeValue, low, ZMod.val_zero]
  congr 1
  omega

end Airbender.Blake2Round.Control.Proofs
