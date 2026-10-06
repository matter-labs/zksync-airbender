import Airbender.Proofs.JumpBranchSlt.PC
import Airbender.Proofs.JumpBranchSlt.Signed
import Airbender.Proofs.Sail.PC

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- One circuit contract for the four actual Sail comparison clauses. -/
theorem comparison_soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    Comparison.circuitModel.SoundnessUnder (Comparison.InterfaceAssumptions (p := p)) Comparison.spec := by
  intro input output w ⟨interface, h, mapping⟩
  have bitResult : output.destination.toBitVec = match input.opcode with
      | .slt | .slti => SailRV32.Functions.zero_extend (m := 32)
          (SailRV32.Functions.bool_to_bit
            (SailRV32.Functions.zopz0zI_s input.left.toBitVec input.right.toBitVec))
      | .sltu | .sltiu => SailRV32.Functions.zero_extend (m := 32)
          (SailRV32.Functions.bool_to_bit
            (SailRV32.Functions.zopz0zI_u input.left.toBitVec input.right.toBitVec)) := by
    cases hop : input.opcode
    case slt | slti =>
      have result := signed_destination hp h interface.selected interface.otherSelectors
        (by simpa [hop] using interface.funct3) interface.nonzeroSelector
        ⟨mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi⟩
        ⟨mapping.outputLo, mapping.outputHi⟩ interface.leftBound interface.rightBound
      change BitVec.ofNat 32 output.destination.value = _
      rw [result]
      by_cases lt : input.left.toBitVec.toInt < input.right.toBitVec.toInt <;>
        simp [lt, SailRV32.Functions.zero_extend, SailRV32.Functions.bool_to_bit,
          SailRV32.Functions.bool_bit_forwards, SailRV32.Functions.zopz0zI_s,
          _root_.Sail.BitVec.zeroExtend]
    case sltu | sltiu =>
      have result := unsigned_destination hp h interface.selected interface.otherSelectors
        (by simpa [hop] using interface.funct3) interface.nonzeroSelector
        ⟨mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi⟩
        ⟨mapping.outputLo, mapping.outputHi⟩ interface.leftBound interface.rightBound
      have comparison : SailRV32.Functions.zopz0zI_u input.left.toBitVec input.right.toBitVec =
          decide (input.left.value < input.right.value) := by
        simp [SailRV32.Functions.zopz0zI_u, _root_.Sail.BitVec.toNatInt,
          Word.toBitVec_toNat interface.leftBound, Word.toBitVec_toNat interface.rightBound]
      simp only [comparison]
      by_cases lt : input.left.value < input.right.value <;>
        simp [Word.toBitVec, result, lt, SailRV32.Functions.zero_extend,
          SailRV32.Functions.bool_to_bit, SailRV32.Functions.bool_bit_forwards,
          _root_.Sail.BitVec.zeroExtend]
  have pc := comparison_pc hp h mapping interface
  apply Sail.retire_of_destination interface.pcRead pc
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have leftRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.leftRead
  have executed : run (Comparison.execution input) prepared =
      run (Sail.writeResult input.rd output.destination) prepared := by
    cases hop : input.opcode
    case slt | sltu =>
      have rightRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs2
        (interface.rightRead (by simp [hop]))
      simp only [Comparison.execution, hop, Sail.writeResult, SailRV32.Functions.execute_RTYPE,
        freeM_bind_assoc, freeM_pure_bind]
      simp only [hop] at bitResult
      rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ rightRead,
        ← bitResult]
    case slti | sltiu =>
      simp only [Comparison.execution, hop, Sail.writeResult, SailRV32.Functions.execute_ITYPE,
        freeM_bind_assoc, freeM_pure_bind]
      simp only [hop] at bitResult
      rw [run_bind_of_ok _ _ _ _ _ leftRead,
        ← interface.signExtension (by simp [hop]), ← bitResult]
  obtain ⟨written, hw⟩ := Sail.write_success input.rd output.destination.toBitVec prepared
  have projected : run (Sail.writeResult input.rd output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS written := by
    simp only [Sail.writeResult]
    rw [run_bind_of_ok _ _ _ _ _ hw]
    rfl
  exact ⟨written, executed.trans projected, projected⟩

end Airbender.JumpBranchSlt.Proofs
