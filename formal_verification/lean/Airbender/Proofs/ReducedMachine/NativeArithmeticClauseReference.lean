import Airbender.Proofs.Arithmetic.Word
import Airbender.Review.Circuits.ReducedMachine.ArithmeticDecoder
import Airbender.Proofs.Sail.PC

namespace Airbender.ReducedMachine.NativeArithmeticClauseProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Execute retained original arithmetic clauses after actual operand and PC
    observations. AUIPC reads the prepared incoming architectural PC. -/
theorem decoded_clause_of_reads {entry : ArithmeticProgramEntry}
    (fields : arithmeticDecoderFields entry.instruction = some entry.data)
    {before after : State} (left operand registerRight pc : Word)
    (leftRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok left.toBitVec before)
    (rightRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok registerRight.toBitVec before)
    (selected : operand = if entry.data.family.useRegister then registerRight else entry.data.immediate)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) before = .ok pc.toBitVec before)
    (written : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (entry.data.family.result left.toBitVec operand.toBitVec pc.toBitVec entry.data.immediate.toBitVec))
      before = .ok () after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  unfold arithmeticDecoderFields at fields
  split at fields
  all_goals try simp only [Native.arithmeticFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       rw [← fields] at leftRead rightRead selected written
       simp_all only [registerClause]
       refine ⟨_,rfl,?_⟩
       simp only [ArithmeticMode.useRegister,ArithmeticMode.result,Bool.false_eq_true,if_false,if_true] at selected written
       try subst operand
       try simp only [Word.ofBitVec_roundtrip] at written
       simp only [SailRV32.Functions.execute_RTYPE,SailRV32.Functions.execute_ITYPE,
         SailRV32.Functions.execute_UTYPE,freeM_bind_assoc,freeM_pure_bind]
       try rw [run_bind_of_ok _ _ _ _ _ leftRead]
       try rw [run_bind_of_ok _ _ _ _ _ rightRead]
       try rw [run_bind_of_ok _ _ _ _ _ pcRead]
       try simp [SailRV32.Functions.sign_extend,Sail.BitVec.signExtend] at written ⊢
       rw [run_bind_of_ok _ _ _ _ _ written]
       rfl)

end Airbender.ReducedMachine.NativeArithmeticClauseProofs
