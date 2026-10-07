import Airbender.Review.JumpBranchSlt.Jump
import Airbender.Proofs.JumpBranchSlt.Jump
import Airbender.Proofs.Sail.ControlFlow

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- JAL and JALR share target/link algebra, native writes and retirement. -/
theorem jump_soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    Jump.circuitModel.SoundnessUnder (Jump.InterfaceAssumptions (p := p)) Jump.spec := by
  intro input output w ⟨interface, h, mapping⟩
  have selected : w 11 + w 12 = 1 := by
    rw [interface.selected.1, interface.selected.2]
    cases input.instruction.indirect <;> simp
  have link := (jump_link hp h selected interface.otherSelectors mapping.initialPC
    interface.initialPCLoBound).1
  have destination : output.destination = ⟨(w 30).val, (w 31).val⟩ := by
    exact congrArg₂ Word.mk mapping.destination.1 mapping.destination.2
  rw [← destination] at link
  obtain ⟨pc, aligned⟩ := jump_pc hp input.instruction.indirect h interface.selected
    interface.otherSelectors mapping.targetWords interface.baseLoBound interface.sourceHiBound
    interface.offsetBound interface.directEven interface.finalPCHiBound
  have writeLink : (do
      SailRV32.Functions.wX_bits input.rd (input.pc.toBitVec + 4)
      pure SailRV32.Functions.RETIRE_SUCCESS) =
      Sail.writeResult input.rd output.destination := by
    by_cases zero : input.rd = Sail.zeroRegister
    · simp only [zero, Sail.writeResult, Sail.write_zero, freeM_pure_bind]
    · have mask : w 15 ≠ 1 := fun masked => zero (interface.zeroDestination.mp masked)
      simp only [mask, ↓reduceIte] at link
      simp only [Sail.writeResult, link]
  apply Sail.retire_of_effects interface.pcRead
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC (input.pc.toBitVec + 4) }
  let targetState : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  obtain ⟨written, write⟩ := Sail.write_success input.rd output.destination.toBitVec targetState
  have projected : run (Sail.writeResult input.rd output.destination) targetState =
      .ok SailRV32.Functions.RETIRE_SUCCESS written := by
    simp only [Sail.writeResult]
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  refine ⟨written, ?_, projected⟩
  have nextRead : run (SailRV32.Functions.get_next_pc ()) prepared =
      .ok (input.pc.toBitVec + 4) prepared := Sail.read_register (by simp [prepared])
  obtain ⟨misa, read⟩ := interface.misaRead
  have read' := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide) read
  have jumped : run (SailRV32.Functions.jump_to output.pc.toBitVec) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS targetState := by
    simpa only [prepared, targetState, Sail.nextPC_overwrite] using Sail.jump_to_aligned aligned read'
  cases instruction : input.instruction with
  | jal imm =>
    have pcRead := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide)
      (show run (SailRV32.readReg .PC) input.before = .ok input.pc.toBitVec input.before from interface.pcRead)
    simp only [instruction, Jump.Instruction.indirect, Bool.false_eq_true, ↓reduceIte,
      Jump.Input.base] at pc
    have extension := interface.signExtension
    simp only [instruction] at extension
    simp only [Jump.execution, instruction, SailRV32.Functions.execute_JAL]
    rw [run_bind_of_ok _ _ _ _ _ nextRead, run_bind_of_ok _ _ _ _ _ pcRead,
      ← extension, ← pc, run_bind_of_ok _ _ _ _ _ jumped]
    change run (do
      SailRV32.Functions.wX_bits input.rd (input.pc.toBitVec + 4)
      pure SailRV32.Functions.RETIRE_SUCCESS) targetState = _
    rw [writeLink]
    exact projected
  | jalr imm =>
    have indirect : input.instruction.indirect = true := by simp [instruction, Jump.Instruction.indirect]
    obtain ⟨privilege, security, config, disabled⟩ := interface.landingPad indirect
    have privilege' := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide) privilege
    have config' := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide) config
    have noPad := Sail.landing_pad_disabled input.rs1 privilege' config' disabled
    have sourceRead := Sail.rX_nextPC (pc := input.pc.toBitVec + 4) input.rs1 (interface.sourceRead indirect)
    simp only [instruction, Jump.Instruction.indirect, ↓reduceIte, Jump.Input.base] at pc
    have extension := interface.signExtension
    simp only [instruction] at extension
    simp only [Jump.execution, instruction, SailRV32.Functions.execute_JALR]
    rw [run_bind_of_ok _ _ _ _ _ noPad, run_bind_of_ok _ _ _ _ _ nextRead,
      run_bind_of_ok _ _ _ _ _ sourceRead, freeM_pure_bind,
      Sail.clear_bit_zero, ← extension, ← pc, run_bind_of_ok _ _ _ _ _ jumped]
    change run (do
      SailRV32.Functions.wX_bits input.rd (input.pc.toBitVec + 4)
      pure SailRV32.Functions.RETIRE_SUCCESS) targetState = _
    rw [writeLink]
    exact projected

end Airbender.JumpBranchSlt.Proofs
