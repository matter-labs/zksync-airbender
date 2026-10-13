import Airbender.Review.Circuits.JumpBranchSlt.Jump
import Airbender.Proofs.Sail.ControlFlow

namespace Airbender.Reference.RiscV.Sail
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open Airbender.JumpBranchSlt
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem retire_jump (input : Jump.Input) (output : Output)
    (link : output.destination.toBitVec = if input.rd = zeroRegister then 0 else input.pc.toBitVec + 4)
    (pc : output.pc.toBitVec = if input.instruction.indirect then
      (input.base.toBitVec + input.offset.toBitVec) &&& 0xfffffffe
      else input.base.toBitVec + input.offset.toBitVec)
    (aligned : output.pc.toBitVec.toNat % 4 = 0)
    (signExtension : input.offset.toBitVec = match input.instruction with
      | .jal imm => SailRV32.Functions.sign_extend (m := 32) imm
      | .jalr imm => SailRV32.Functions.sign_extend (m := 32) imm)
    (sourceRead : input.instruction.indirect = true →
      run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.source.toBitVec input.before)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before)
    (misaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before)
    (landingPad : input.instruction.indirect = true →
      run (SailRV32.readReg .cur_privilege) input.before = .ok .Machine input.before ∧
      ∃ security, run (SailRV32.readReg .mseccfg) input.before = .ok security input.before ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0) : Jump.spec input output := by
  have writeLink : (do
      SailRV32.Functions.wX_bits input.rd (input.pc.toBitVec + 4)
      pure SailRV32.Functions.RETIRE_SUCCESS) =
      Sail.writeResult input.rd output.destination := by
    by_cases zero : input.rd = Sail.zeroRegister
    · simp only [zero, Sail.writeResult, Sail.write_zero, freeM_pure_bind]
    · simp only [zero, ↓reduceIte] at link
      simp only [Sail.writeResult, link]
  apply Sail.retire_of_effects pcRead
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
  obtain ⟨misa, read⟩ := misaRead
  have read' := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide) read
  have jumped : run (SailRV32.Functions.jump_to output.pc.toBitVec) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS targetState := by
    simpa only [prepared, targetState, Sail.nextPC_overwrite] using Sail.jump_to_aligned aligned read'
  cases instruction : input.instruction with
  | jal imm =>
    have pcRead := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide)
      (show run (SailRV32.readReg .PC) input.before = .ok input.pc.toBitVec input.before from pcRead)
    simp only [instruction, Jump.Instruction.indirect, Bool.false_eq_true, ↓reduceIte,
      Jump.Input.base] at pc
    have extension := signExtension
    simp only [instruction] at extension
    simp only [Jump.execution, Jump.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, instruction, SailRV32.Functions.execute_JAL]
    rw [run_bind_of_ok _ _ _ _ _ nextRead, run_bind_of_ok _ _ _ _ _ pcRead,
      ← extension, ← pc, run_bind_of_ok _ _ _ _ _ jumped]
    change run (do
      SailRV32.Functions.wX_bits input.rd (input.pc.toBitVec + 4)
      pure SailRV32.Functions.RETIRE_SUCCESS) targetState = _
    rw [writeLink]
    exact projected
  | jalr imm =>
    have indirect : input.instruction.indirect = true := by simp [instruction, Jump.Instruction.indirect]
    obtain ⟨privilege, security, config, disabled⟩ := landingPad indirect
    have privilege' := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide) privilege
    have config' := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide) config
    have noPad := Sail.landing_pad_disabled input.rs1 privilege' config' disabled
    have sourceRead := Sail.rX_nextPC (pc := input.pc.toBitVec + 4) input.rs1 (sourceRead indirect)
    simp only [instruction, Jump.Instruction.indirect, ↓reduceIte, Jump.Input.base] at pc
    have extension := signExtension
    simp only [instruction] at extension
    simp only [Jump.execution, Jump.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, instruction, SailRV32.Functions.execute_JALR]
    rw [run_bind_of_ok _ _ _ _ _ noPad, run_bind_of_ok _ _ _ _ _ nextRead,
      run_bind_of_ok _ _ _ _ _ sourceRead, freeM_pure_bind,
      Sail.clear_bit_zero, ← extension, ← pc, run_bind_of_ok _ _ _ _ _ jumped]
    change run (do
      SailRV32.Functions.wX_bits input.rd (input.pc.toBitVec + 4)
      pure SailRV32.Functions.RETIRE_SUCCESS) targetState = _
    rw [writeLink]
    exact projected


end Airbender.Reference.RiscV.Sail
