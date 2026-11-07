import Airbender.Proofs.Arithmetic.Word
import Airbender.Review.Circuits.ReducedMachine.ComparisonDecoder
import Airbender.Proofs.Sail.PC

namespace Airbender.ReducedMachine.NativeComparisonClauseProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original signed comparison primitive and one-bit zero extension. -/
theorem original_signed_result (left right : BitVec 32) :
    SailRV32.Functions.zero_extend (m := 32) (SailRV32.Functions.bool_to_bit
      (SailRV32.Functions.zopz0zI_s left right)) =
      BitVec.ofNat 32 (if left.toInt < right.toInt then 1 else 0) := by
  by_cases lt : left.toInt < right.toInt <;>
    simp [SailRV32.Functions.zero_extend,SailRV32.Functions.bool_to_bit,
      SailRV32.Functions.bool_bit_forwards,SailRV32.Functions.zopz0zI_s,
      Sail.BitVec.zeroExtend,lt]

/-- Original unsigned comparison observes all32bits through natural decoding. -/
theorem original_unsigned_result (left right : BitVec 32) :
    SailRV32.Functions.zero_extend (m := 32) (SailRV32.Functions.bool_to_bit
      (SailRV32.Functions.zopz0zI_u left right)) =
      BitVec.ofNat 32 (if left.toNat < right.toNat then 1 else 0) := by
  by_cases lt : left.toNat < right.toNat <;>
    simp [SailRV32.Functions.zero_extend,SailRV32.Functions.bool_to_bit,
      SailRV32.Functions.bool_bit_forwards,SailRV32.Functions.zopz0zI_u,
      Sail.BitVec.zeroExtend,Sail.BitVec.toNatInt,lt]

/-- Execute retained original comparison clauses after actual operand
    observations. All register/immediate constructors retain original x0 behavior. -/
theorem decoded_clause_of_reads {entry : ComparisonProgramEntry}
    (fields : comparisonDecoderFields entry.instruction = some entry.data)
    {before after : State} (left operand registerRight : Word)
    (leftRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok left.toBitVec before)
    (rightRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok registerRight.toBitVec before)
    (selected : operand = if entry.data.family.useRegister then registerRight else entry.data.immediate)
    (written : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (entry.data.family.result left.toBitVec operand.toBitVec))
      before = .ok () after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  unfold comparisonDecoderFields at fields
  split at fields
  all_goals try simp only [Native.comparisonFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       rw [← fields] at leftRead rightRead selected written
       simp_all only [registerClause]
       refine ⟨_,rfl,?_⟩
       simp only [ComparisonMode.result,Bool.false_eq_true,if_false,if_true] at selected written
       try subst operand
       try simp only [Word.ofBitVec_roundtrip] at written
       simp only [SailRV32.Functions.execute_RTYPE,SailRV32.Functions.execute_ITYPE,
         freeM_bind_assoc,freeM_pure_bind]
       try rw [run_bind_of_ok _ _ _ _ _ leftRead]
       try rw [run_bind_of_ok _ _ _ _ _ rightRead]
       simp only [original_signed_result,original_unsigned_result]
       try simp [SailRV32.Functions.sign_extend,Sail.BitVec.signExtend] at written ⊢
       rw [run_bind_of_ok _ _ _ _ _ written]
       rfl)

end Airbender.ReducedMachine.NativeComparisonClauseProofs
