import Airbender.Proofs.Arithmetic.Word
import Airbender.Review.Circuits.ReducedMachine.ShiftOperand
import Airbender.Proofs.Sail.PC

namespace Airbender.ReducedMachine.NativeShiftClauseProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native SRAI retains its funct7 encoding; original Sail uses only the low
    five amount bits. Both original legal immediate encodings agree exactly. -/
theorem encoded_shift_amount (amount : BitVec 6)
    (arithmetic : Bool) :
    ((BitVec.ofNat 32 (amount.toNat + if arithmetic then 1024 else 0)).extractLsb' 0 5).toNat =
      (amount.extractLsb' 0 5).toNat := by
  cases arithmetic <;> norm_num [BitVec.extractLsb',BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]; omega

private theorem encoded_arithmetic_amount (amount : BitVec 6) :
    ((BitVec.ofNat 32 (amount.toNat + 1024)).extractLsb' 0 5).toNat =
      (amount.extractLsb' 0 5).toNat := by
  simpa only [if_true] using encoded_shift_amount amount true

private theorem extended_amount (amount : BitVec 6) :
    ((BitVec.ofNat 32 amount.toNat).extractLsb' 0 5).toNat = (amount.extractLsb' 0 5).toNat := by
  simpa only [Bool.false_eq_true,if_false,Nat.add_zero] using encoded_shift_amount amount false

private theorem sail_shift_left (x : BitVec 32) {n : Nat} (amount : BitVec n) :
    _root_.Sail.shift_bits_left x (_root_.Sail.BitVec.extractLsb amount
      ((SailRV32.Functions.log2_xlen : Int) - 1).toNat 0) = x <<< (amount.extractLsb' 0 5).toNat := rfl
private theorem sail_shift_right (x : BitVec 32) {n : Nat} (amount : BitVec n) :
    _root_.Sail.shift_bits_right x (_root_.Sail.BitVec.extractLsb amount
      ((SailRV32.Functions.log2_xlen : Int) - 1).toNat 0) = x >>> (amount.extractLsb' 0 5).toNat := rfl
private theorem sail_shift_arithmetic (x : BitVec 32) {n : Nat} (amount : BitVec n) :
    SailRV32.Functions.shift_bits_right_arith x (_root_.Sail.BitVec.extractLsb amount
      ((SailRV32.Functions.log2_xlen : Int) - 1).toNat 0) = x.sshiftRight (amount.extractLsb' 0 5).toNat := rfl

/-- Execute the original pinned clauses using original decoding, actual GPR
    observations and the selected operand. No replacement instruction is built. -/
theorem decoded_clause_of_reads {entry : ShiftProgramEntry}
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    {before after : State} (left operand registerRight : Word)
    (leftRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok left.toBitVec before)
    (rightRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok registerRight.toBitVec before)
    (selected : operand = if shiftUsesRegister entry.instruction then registerRight else entry.data.immediate)
    (written : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (entry.data.family.result left.toBitVec (operand.toBitVec.extractLsb' 0 5).toNat)) before = .ok () after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  unfold shiftDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [Native.shiftFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       rw [← fields] at leftRead rightRead selected written
       simp_all only [registerClause]
       refine ⟨_,rfl,?_⟩
       simp only [shiftUsesRegister,Bool.false_eq_true,if_false,if_true] at selected written
       try subst operand
       simp only [SailRV32.Functions.execute_RTYPE,SailRV32.Functions.execute_SHIFTIOP,freeM_bind_assoc,freeM_pure_bind]
       rw [run_bind_of_ok _ _ _ _ _ leftRead]
       try rw [run_bind_of_ok _ _ _ _ _ rightRead]
       simp only [ShiftMode.result] at written
       try simp only [sail_shift_left,sail_shift_right,sail_shift_arithmetic]
       try simp only [Word.ofBitVec_roundtrip] at written
       try rw [extended_amount] at written
       try rw [encoded_arithmetic_amount] at written
       rw [run_bind_of_ok _ _ _ _ _ written]
       rfl)

end Airbender.ReducedMachine.NativeShiftClauseProofs
