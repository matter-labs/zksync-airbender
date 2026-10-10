import Airbender.Proofs.Sail.Binop
import Airbender.Proofs.Arithmetic.ShiftAssembly

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
set_option warningAsError true

def shiftCount (input : Airbender.ShiftBinop.Input) : Nat :=
  if input.operation = .rev8 then 0 else
    (if input.immediate then input.encodedImmediate.extractLsb' 0 5 else input.right.extractLsb' 0 5).toNat

private theorem sail_shift_left (x : BitVec 32) (amount : BitVec n) :
    _root_.Sail.shift_bits_left x amount = x <<< amount.toNat := rfl
private theorem sail_shift_right (x : BitVec 32) (amount : BitVec n) :
    _root_.Sail.shift_bits_right x amount = x >>> amount.toNat := rfl
private theorem sail_shift_arithmetic (x : BitVec 32) (amount : BitVec n) :
    SailRV32.Functions.shift_bits_right_arith x amount = x.sshiftRight amount.toNat := rfl

theorem retire_shift (input : Airbender.ShiftBinop.Input) (output : Output)
    (shift : input.operation.isShift = true)
    (leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left input.before)
    (rightRead : input.immediate = false → input.operation ≠ .rev8 →
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before)
    (successor : output.pc.toBitVec = input.pc.toBitVec + 4)
    (result : output.destination.toBitVec = Verification.shiftOperation input.operation.tag input.left (shiftCount input)) :
    Airbender.ShiftBinop.spec input output := by
  apply retire_of_destination pcRead successor
  let prepared : State := { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have left := rX_nextPC (pc := output.pc.toBitVec) input.rs1 leftRead
  have same : run (Airbender.ShiftBinop.execution input) prepared =
      run (writeResult input.rd output.destination) prepared := by
    cases operation : input.operation <;> simp [operation, Airbender.ShiftBinop.Operation.isShift] at shift
    all_goals cases form : input.immediate
    all_goals simp only [Airbender.ShiftBinop.execution, operation, form,
      writeResult, SailRV32.Functions.execute_RTYPE, SailRV32.Functions.execute_SHIFTIOP,
      SailRV32.Functions.execute_REV8, freeM_bind_assoc, freeM_pure_bind]
    all_goals rw [run_bind_of_ok _ _ _ _ _ left]
    all_goals first
      | (have right := rX_nextPC (pc := output.pc.toBitVec) input.rs2
           (rightRead form (by rw [operation]; decide))
         rw [run_bind_of_ok _ _ _ _ _ right, result]
         simp [Verification.shiftOperation, shiftCount, operation, form,
           Airbender.ShiftBinop.Operation.tag, prepared, sail_shift_left, sail_shift_right,
           sail_shift_arithmetic, _root_.Sail.BitVec.extractLsb, SailRV32.Functions.log2_xlen, BitVec.extractLsb])
      | (rw [result]
         simp [Verification.shiftOperation, shiftCount, operation, form,
           Airbender.ShiftBinop.Operation.tag, prepared, sail_shift_left, sail_shift_right,
           sail_shift_arithmetic, _root_.Sail.BitVec.extractLsb, SailRV32.Functions.log2_xlen, BitVec.extractLsb])
  obtain ⟨after, write⟩ := write_success input.rd output.destination.toBitVec prepared
  have projected : run (writeResult input.rd output.destination) prepared = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold writeResult
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨after, same.trans projected, projected⟩

end Airbender.Reference.RiscV.Sail
