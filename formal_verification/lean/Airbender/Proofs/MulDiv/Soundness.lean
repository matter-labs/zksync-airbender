import Airbender.Review.MulDiv.Model
import Airbender.Proofs.MulDiv.Product
import Airbender.Proofs.Sail.PC

namespace Airbender.MulDiv.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

theorem division_soundness {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
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
  let result : Nat := if input.right.value = 0 then
      if input.remainder then input.left.value else 4294967295
    else if input.remainder then input.left.value % input.right.value
      else input.left.value / input.right.value
  have destination : output.destination.toBitVec = BitVec.ofNat 32 result := by
    by_cases zero : input.right.value = 0
    · have zeroFields : w 24 = 0 ∧ w 25 = 0 := by
        simpa [Word.value, mapping.rightLo, mapping.rightHi, limbBase,
          ZMod.val_eq_zero] using zero
      have value := division_by_zero (by omega) input.remainder h interface.selected
        interface.otherSelectors zeroFields
      dsimp [result]
      rw [if_pos zero]
      cases operation : input.remainder <;> simpa [operation, Word.toBitVec, Word.value,
        mapping.outputLo, mapping.outputHi, mapping.leftLo, mapping.leftHi] using value
    · have nonzero : (⟨(w 24).val, (w 25).val⟩ : Word).value ≠ 0 := by
        simpa [Word.value, mapping.rightLo, mapping.rightHi] using zero
      have value := division_nonzero hp inverse h input.remainder interface.selected
        interface.otherSelectors leftBound nonzero
      have outputValue : output.destination.value = result := by
        dsimp [result]
        rw [if_neg zero]
        simpa [Word.value, mapping.outputLo, mapping.outputHi,
          mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi] using value
      simp only [Word.toBitVec, outputValue]
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
    cases operation : input.remainder
    · simp only [Bool.false_eq_true, ↓reduceIte, SailRV32.Functions.execute_DIV]
      rw [run_bind_of_ok _ _ _ _ _ leftRead,
        run_bind_of_ok _ _ _ _ _ rightRead]
      simp [SailRV32.Functions.not, _root_.Sail.BitVec.toNatInt,
        Word.toBitVec_toNat interface.leftBound, Word.toBitVec_toNat rightBound,
        result, operation] at destination ⊢
      rw [destination]
      have maxValue : SailRV32.Functions.to_bits_truncate (l := 32) (-1) =
          BitVec.ofNat 32 4294967295 := by decide
      by_cases zero : input.right.value = 0 <;> simp only [zero, if_true, if_false]
      · rw [maxValue]
      · rw [← Int.natCast_ediv, Sail.truncate_nat]
    · simp only [↓reduceIte, SailRV32.Functions.execute_REM]
      rw [run_bind_of_ok _ _ _ _ _ leftRead,
        run_bind_of_ok _ _ _ _ _ rightRead]
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
