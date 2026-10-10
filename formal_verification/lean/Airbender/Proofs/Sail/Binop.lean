import Airbender.Review.ShiftBinop.Model
import Airbender.Proofs.Sail.PC
import Airbender.Proofs.ByteTables

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
set_option warningAsError true

theorem retire_binary (input : Airbender.ShiftBinop.Input) (output : Output)
    (binary : input.operation.isShift = false)
    (leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left input.before)
    (rightRead : input.immediate = false →
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before)
    (immediateValue : input.immediate = true →
      input.right = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before)
    (successor : output.pc.toBitVec = input.pc.toBitVec + 4)
    (result : output.destination.toBitVec = Verification.byteOperation input.operation.tag input.left input.right) :
    Airbender.ShiftBinop.spec input output := by
  apply retire_of_destination pcRead successor
  let prepared : State := { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have left := rX_nextPC (pc := output.pc.toBitVec) input.rs1 leftRead
  have same : run (Airbender.ShiftBinop.execution input) prepared =
      run (writeResult input.rd output.destination) prepared := by
    cases operation : input.operation <;> simp [operation, Airbender.ShiftBinop.Operation.isShift] at binary
    all_goals cases form : input.immediate
    all_goals simp only [Airbender.ShiftBinop.execution, operation, form,
      writeResult, SailRV32.Functions.execute_RTYPE, SailRV32.Functions.execute_ITYPE,
      freeM_bind_assoc, freeM_pure_bind]
    all_goals rw [run_bind_of_ok _ _ _ _ _ left]
    all_goals first
      | (have right := rX_nextPC (pc := output.pc.toBitVec) input.rs2 (rightRead form)
         rw [run_bind_of_ok _ _ _ _ _ right, result]
         simp [Verification.byteOperation, operation, Airbender.ShiftBinop.Operation.tag, prepared])
      | (rw [result, immediateValue form]
         simp [Verification.byteOperation, operation, Airbender.ShiftBinop.Operation.tag, prepared])
  obtain ⟨after, write⟩ := write_success input.rd output.destination.toBitVec prepared
  have projected : run (writeResult input.rd output.destination) prepared = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold writeResult
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨after, same.trans projected, projected⟩

theorem retire_binary_register (input : Airbender.ShiftBinop.Input) (output : Output)
    (binary : input.operation.isShift = false) (register : input.immediate = false)
    (leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left input.before)
    (rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before)
    (successor : output.pc.toBitVec = input.pc.toBitVec + 4)
    (result : output.destination.toBitVec = Verification.byteOperation input.operation.tag input.left input.right) :
    Airbender.ShiftBinop.spec input output :=
  retire_binary input output binary leftRead (fun _ => rightRead)
    (fun form => by simp [register] at form) pcRead successor result

end Airbender.Reference.RiscV.Sail
