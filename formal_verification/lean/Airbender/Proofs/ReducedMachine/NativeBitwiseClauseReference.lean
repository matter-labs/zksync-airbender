import Airbender.Proofs.Arithmetic.Word
import Airbender.Review.Circuits.ReducedMachine.BitwiseDecoder
import Airbender.Proofs.Sail.PC

namespace Airbender.ReducedMachine.NativeBitwiseClauseProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Execute retained original bitwise clauses after actual operand
    observations. All register/immediate constructors retain original x0 behavior. -/
theorem decoded_clause_of_reads {entry : BitwiseProgramEntry}
    (fields : bitwiseDecoderFields entry.instruction = some entry.data)
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
  unfold bitwiseDecoderFields at fields
  split at fields
  all_goals try simp only [Native.bitwiseFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       rw [← fields] at leftRead rightRead selected written
       simp_all only [registerClause]
       refine ⟨_,rfl,?_⟩
       simp only [BitwiseMode.result,Verification.byteOperation,Verification.BinaryKind.tag,Bool.false_eq_true,if_false,if_true] at selected written
       try subst operand
       try simp only [Word.ofBitVec_roundtrip] at written
       simp only [SailRV32.Functions.execute_RTYPE,SailRV32.Functions.execute_ITYPE,
         freeM_bind_assoc,freeM_pure_bind]
       try rw [run_bind_of_ok _ _ _ _ _ leftRead]
       try rw [run_bind_of_ok _ _ _ _ _ rightRead]
       try simp [SailRV32.Functions.sign_extend,Sail.BitVec.signExtend] at written ⊢
       rw [run_bind_of_ok _ _ _ _ _ written]
       rfl)

end Airbender.ReducedMachine.NativeBitwiseClauseProofs
