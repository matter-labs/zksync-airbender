import Slop.Bigint.ArtifactChecks
import Human.Circuits.Bigint.Control
import Slop.Constraints
import Slop.Arithmetic.Lemmas

namespace Airbender.Bigint.Control.Proofs
open Arithmetic
open scoped BigOperators

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem control_bits {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 3)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 8, w Variables.controlBits[i] = 0 ∨ w Variables.controlBits[i] = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h ⟨92 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, Variables.controlBits,
    mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
  all_goals exact flag

theorem opcode_exclusivity {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (∑ i : Fin 7, (w Variables.operations[i]).val) ≤ 1 := by
  have flag := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at flag
  let total : ZMod p := ∑ i : Fin 7, w Variables.operations[i]
  have bit : total = 0 ∨ total = 1 := by
    rcases flag with zero | one
    · left
      norm_num [total, Fin.sum_univ_succ, Variables.operations]
      linear_combination zero
    · right
      norm_num [total, Fin.sum_univ_succ, Variables.operations]
      linear_combination one
  have flags : ∀ i : Fin 7, w Variables.operations[i] = 0 ∨ w Variables.operations[i] = 1 := by
    intro i
    fin_cases i <;> first
      | exact control_bits h 0 | exact control_bits h 1 | exact control_bits h 2
      | exact control_bits h 3 | exact control_bits h 4 | exact control_bits h 5 | exact control_bits h 7
  exact boolean_sum_le_one (by omega) flags bit rfl

theorem mask_bounded (bits : Vector Bool 8) : mask bits < 256 := by
  have bit (i : Fin 8) : bits[i].toNat ≤ 1 := by cases bits[i] <;> decide
  have bound : mask bits ≤ ∑ i : Fin 8, 2 ^ i.val * 1 :=
    Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (bit i))
  have total : (∑ i : Fin 8, 2 ^ i.val * 1) = 255 := by decide
  omega

/-- The same native field sum is interpreted as a byte only after proving its
    natural bound; neither the incoming high limb nor setup rows are constrained. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 256 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    Properties.Soundness (circuitModel setup).relation spec := by
  intro input output w ⟨h, mapping⟩
  have bitCast (i : Fin 8) : (output.bits[i].toNat : ZMod p) = w Variables.controlBits[i] := by
    rw [mapping.bits]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    have oneVal : (1 : ZMod p).val = 1 := ZMod.val_one (by omega)
    have native := control_bits h i
    simp [Variables.controlBits, Fin.getElem_fin] at native
    rcases native with zero | one
    · simp [zero]
    · simp [one, oneVal]
  have bitValue (i : Fin 8) : (w Variables.controlBits[i]).val = output.bits[i].toNat := by
    rw [← bitCast i]
    exact ZMod.val_natCast_of_lt (lt_of_le_of_lt
      (show output.bits[i].toNat ≤ 1 by cases output.bits[i] <;> decide) (by omega))
  have read := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨91, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at read high
  have field : (mask output.bits : ZMod p) = w 55 := by
    simp only [mask, Nat.cast_sum, Nat.cast_mul, bitCast]
    norm_num [Fin.sum_univ_succ, Variables.controlBits]
    linear_combination read
  have bound := mask_bounded output.bits
  have decoded : input.lo = mask output.bits := by
    rw [mapping.inputWord]
    change (w 55).val = mask output.bits
    rw [← field]
    exact ZMod.val_natCast_of_lt (by omega)
  have count : operationCount output.bits = ∑ i : Fin 7, (w Variables.operations[i]).val := by
    unfold operationCount
    apply Finset.sum_congr rfl
    intro i _
    fin_cases i <;> first
      | exact (bitValue 0).symm | exact (bitValue 1).symm | exact (bitValue 2).symm
      | exact (bitValue 3).symm | exact (bitValue 4).symm | exact (bitValue 5).symm
      | exact (bitValue 7).symm
  refine ⟨decoded, by omega, ?_, ?_⟩
  · rw [count]
    exact opcode_exclusivity (by omega) h
  · rw [mapping.outputWord]
    change (w 58).val = 0
    simp [high]

end Airbender.Bigint.Control.Proofs
