import Airbender.Proofs.JumpBranchSlt.PC
import Airbender.Proofs.Sail.PC

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- Local comparison arithmetic meets the actual generated SLTU execution clause. -/
theorem sltu_soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    Sltu.circuitModel.SoundnessUnder (Sltu.InterfaceAssumptions (p := p)) Sltu.spec := by
  intro input output w ⟨interface, h, mapping⟩
  have result := unsigned_destination hp h interface.selected interface.otherSelectors
    interface.immediate interface.funct3 interface.nonzeroSelector
    ⟨mapping.leftLo, mapping.leftHi, mapping.rightLo, mapping.rightHi⟩
    ⟨mapping.outputLo, mapping.outputHi⟩ interface.leftBound interface.rightBound
  have pc := sltu_pc hp h mapping interface
  apply Sail.retire_of_destination interface.pcRead pc
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have leftRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.leftRead
  have rightRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs2 interface.rightRead
  have bitResult : output.destination.toBitVec = SailRV32.Functions.zero_extend (m := 32)
      (SailRV32.Functions.bool_to_bit
        (SailRV32.Functions.zopz0zI_u input.left.toBitVec input.right.toBitVec)) := by
    have comparison : SailRV32.Functions.zopz0zI_u input.left.toBitVec input.right.toBitVec =
        decide (input.left.value < input.right.value) := by
      simp [SailRV32.Functions.zopz0zI_u, _root_.Sail.BitVec.toNatInt,
        Word.toBitVec_toNat interface.leftBound, Word.toBitVec_toNat interface.rightBound]
    rw [comparison]
    by_cases lt : input.left.value < input.right.value <;>
      simp [Word.toBitVec, result, lt, SailRV32.Functions.zero_extend,
        SailRV32.Functions.bool_to_bit, SailRV32.Functions.bool_bit_forwards,
        _root_.Sail.BitVec.zeroExtend]
  have executed : run (Sltu.execution input) prepared =
      run (Sail.writeResult input.rd output.destination) prepared := by
    simp only [Sltu.execution, Sail.writeResult, SailRV32.Functions.execute_RTYPE,
      freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ rightRead,
      ← bitResult]
  obtain ⟨written, hw⟩ := Sail.write_success input.rd output.destination.toBitVec prepared
  have projected : run (Sail.writeResult input.rd output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS written := by
    simp only [Sail.writeResult]
    rw [run_bind_of_ok _ _ _ _ _ hw]
    rfl
  exact ⟨written, executed.trans projected, projected⟩

end Airbender.JumpBranchSlt.Proofs
