import Airbender.Review.MulDiv.Model
import Airbender.Proofs.MulDiv.Product
import Airbender.Proofs.Sail.PC

namespace Airbender.MulDiv.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

-- These arithmetic expressions are proof intermediates; the public reference
-- remains the original Sail execution in Review/MulDiv/Model.lean.
private def result (operation : Operation) (left right : Nat) : Nat :=
  match operation with
  | .mul => (left * right) % wordModulus
  | .mulhu => (left * right) / wordModulus
  | .divu => if right = 0 then 4294967295 else left / right
  | .remu => if right = 0 then left else left % right

private theorem division_destination {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (remainder : Bool)
    (selected : w 12 = (if remainder then 0 else 1) ∧ w 13 = (if remainder then 1 else 0))
    (other : w 10 = 0 ∧ w 11 = 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase) :
    (⟨(w 28).val, (w 29).val⟩ : Word).toBitVec = BitVec.ofNat 32
      (if (⟨(w 24).val, (w 25).val⟩ : Word).value = 0 then
        if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).value else 4294967295
      else if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).value %
        (⟨(w 24).val, (w 25).val⟩ : Word).value
      else (⟨(w 20).val, (w 21).val⟩ : Word).value /
        (⟨(w 24).val, (w 25).val⟩ : Word).value) := by
  by_cases zero : (⟨(w 24).val, (w 25).val⟩ : Word).value = 0
  · have zeroFields : w 24 = 0 ∧ w 25 = 0 := by
      simpa [Word.value, limbBase, ZMod.val_eq_zero] using zero
    have value := division_by_zero (by omega) remainder h selected other zeroFields
    cases remainder <;> simpa [zero, Word.toBitVec] using value
  · have value := division_nonzero hp inverse h remainder selected other leftBound zero
    simp only [if_neg zero, Word.toBitVec, value]

theorem soundness {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec := by
  intro input output w ⟨interface, h, mapping⟩
  have leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase := by
    rw [← mapping.leftLo, ← mapping.leftHi]
    exact interface.leftBound
  have bytes := byte_values (by omega) h
  have rightBound : input.right.Bounded := by
    rw [Word.Bounded, mapping.rightLo, mapping.rightHi]
    exact ⟨(bytes ⟨0, by decide⟩).1, (bytes ⟨1, by decide⟩).1⟩
  have s0 := interface.selected ⟨0, by decide⟩
  have s1 := interface.selected ⟨1, by decide⟩
  have s2 := interface.selected ⟨2, by decide⟩
  have s3 := interface.selected ⟨3, by decide⟩
  have destination : output.destination.toBitVec =
      BitVec.ofNat 32 (result input.operation input.left.value input.right.value) := by
    cases operation : input.operation
    · have value := multiplication_result hp inverse h false
        (by simpa [operation, Operation.selector] using interface.selected) leftBound
      simpa [Word.toBitVec, Word.value, mapping.outputLo, mapping.outputHi,
        mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi, operation, result] using
        congrArg (BitVec.ofNat 32) value
    · have value := multiplication_result hp inverse h true
        (by simpa [operation, Operation.selector] using interface.selected) leftBound
      simpa [Word.toBitVec, Word.value, mapping.outputLo, mapping.outputHi,
        mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi, operation, result] using
        congrArg (BitVec.ofNat 32) value
    · have value := division_destination hp inverse h false
        ⟨by simpa [operation, Operation.selector] using s2,
         by simpa [operation, Operation.selector] using s3⟩
        ⟨by simpa [operation, Operation.selector] using s0,
         by simpa [operation, Operation.selector] using s1⟩ leftBound
      simpa [Word.toBitVec, Word.value, mapping.outputLo, mapping.outputHi,
        mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi, operation, result] using value
    · have value := division_destination hp inverse h true
        ⟨by simpa [operation, Operation.selector] using s2,
         by simpa [operation, Operation.selector] using s3⟩
        ⟨by simpa [operation, Operation.selector] using s0,
         by simpa [operation, Operation.selector] using s1⟩ leftBound
      simpa [Word.toBitVec, Word.value, mapping.outputLo, mapping.outputHi,
        mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi, operation, result] using value
  have pc := pc_successor (by omega) inverse h
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ interface.initialPCBound
  apply Sail.retire_of_destination interface.pcRead pc.2.2
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have leftRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.leftRead
  have rightRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs2 interface.rightRead
  have same : run (execution input) prepared =
      run (Sail.writeResult input.rd output.destination) prepared := by
    unfold execution Sail.writeResult
    cases operation : input.operation
    · simp only [SailRV32.Functions.execute_MUL, SailRV32.Functions.xlen]
      rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ rightRead]
      rw [Sail.mul_low_signed, destination]
      have modulo (n : Nat) : BitVec.ofNat 32 (n % wordModulus) = BitVec.ofNat 32 n := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ofNat, wordModulus, show 2 ^ 32 = 4294967296 by decide]
      simp [result, operation, Word.toBitVec, ← BitVec.ofNat_mul, modulo, prepared]
    · simp only [SailRV32.Functions.execute_MUL, SailRV32.Functions.xlen]
      rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ rightRead]
      rw [Sail.mul_high_unsigned, destination]
      simp [result, operation, Word.toBitVec_toNat interface.leftBound,
        Word.toBitVec_toNat rightBound, wordModulus, prepared]
    · simp only [SailRV32.Functions.execute_DIV]
      rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ rightRead]
      simp [SailRV32.not, _root_.Sail.BitVec.toNatInt,
        Word.toBitVec_toNat interface.leftBound, Word.toBitVec_toNat rightBound,
        result, operation] at destination ⊢
      rw [destination]
      have maxValue : SailRV32.Functions.to_bits_truncate (l := 32) (-1) =
          BitVec.ofNat 32 4294967295 := by decide
      by_cases zero : input.right.value = 0 <;> simp only [zero, if_true, if_false]
      · rw [maxValue]
      · rw [← Int.natCast_ediv, Sail.truncate_nat]
    · simp only [SailRV32.Functions.execute_REM]
      rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ rightRead]
      simp [_root_.Sail.BitVec.toNatInt, Word.toBitVec_toNat interface.leftBound,
        Word.toBitVec_toNat rightBound, result, operation] at destination ⊢
      rw [destination]
      by_cases zero : input.right.value = 0 <;> simp only [zero, if_true, if_false]
      · rw [Sail.truncate_nat]
      · rw [← Int.ofNat_tmod, Sail.truncate_nat]
  obtain ⟨after, write⟩ := Sail.write_success input.rd output.destination.toBitVec prepared
  have projected : run (Sail.writeResult input.rd output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold Sail.writeResult
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨after, same.trans projected, projected⟩

end Airbender.MulDiv.Proofs
