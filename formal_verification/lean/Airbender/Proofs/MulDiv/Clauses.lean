import Airbender.Review.Circuits.MulDiv.Sail
import Airbender.Proofs.MulDiv.Writes
import Airbender.Proofs.MulDiv.Decoder
import Airbender.Review.Helpers.Memory.MulDiv
import Airbender.Proofs.Sail.PC

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification

/-- Successful original decoding fixes the complete original instruction. -/
theorem decoder_instruction {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data) :
    entry.instruction = instruction entry.data.family entry.data.rs1 entry.data.rs2 entry.data.rd := by
  unfold decoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       rw [← fields]
       simpa only [instruction] using (by assumption : entry.instruction = _))

/-- The four original Sail clauses compute the native unsigned numerical result.
    This is proof assembly over pinned clauses, not replacement instruction semantics. -/
theorem clause_of_reads {before after : State} (op : Operation) (rs1 rs2 rd : BitVec 5)
    (left right : Word) (leftBound : left.Bounded) (rightBound : right.Bounded)
    (leftRead : run (SailRV32.Functions.rX_bits (.Regidx rs1)) before = .ok left.toBitVec before)
    (rightRead : run (SailRV32.Functions.rX_bits (.Regidx rs2)) before = .ok right.toBitVec before)
    (written : run (SailRV32.Functions.wX_bits (.Regidx rd)
      (BitVec.ofNat 32 (op.result left right))) before = .ok () after) :
    run (clause op rs1 rs2 rd) before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  cases op
  · simp only [clause,SailRV32.Functions.execute_MUL,SailRV32.Functions.xlen]
    rw [run_bind_of_ok _ _ _ _ _ leftRead,run_bind_of_ok _ _ _ _ _ rightRead,mul_low_signed]
    have modulo (n : Nat) : BitVec.ofNat 32 (n % wordModulus) = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat,wordModulus,show 2^32 = 4294967296 by decide]
    have value : left.toBitVec * right.toBitVec =
        BitVec.ofNat 32 (Operation.mul.result left right) := by
      simp [Operation.result,Word.toBitVec,← BitVec.ofNat_mul,modulo]
    rw [value,run_bind_of_ok _ _ _ _ _ written]
    rfl
  · simp only [clause,SailRV32.Functions.execute_MUL,SailRV32.Functions.xlen]
    rw [run_bind_of_ok _ _ _ _ _ leftRead,run_bind_of_ok _ _ _ _ _ rightRead,mul_high_unsigned]
    have value : BitVec.ofNat 32 (left.toBitVec.toNat * right.toBitVec.toNat / 4294967296) =
        BitVec.ofNat 32 (Operation.mulhu.result left right) := by
      simp [Operation.result,Word.toBitVec_toNat leftBound,Word.toBitVec_toNat rightBound,wordModulus]
    rw [value,run_bind_of_ok _ _ _ _ _ written]
    rfl
  · simp only [clause,SailRV32.Functions.execute_DIV]
    rw [run_bind_of_ok _ _ _ _ _ leftRead,run_bind_of_ok _ _ _ _ _ rightRead]
    simp [SailRV32.not,_root_.Sail.BitVec.toNatInt,Word.toBitVec_toNat leftBound,
      Word.toBitVec_toNat rightBound]
    by_cases zero : right.value = 0
    · have maxValue : SailRV32.Functions.to_bits_truncate (l := 32) (-1) =
          BitVec.ofNat 32 (wordModulus - 1) := by decide
      simp only [zero,if_true]
      rw [maxValue]
      simp only [Operation.result,zero,if_true] at written
      rw [run_bind_of_ok _ _ _ _ _ written]
      rfl
    · simp only [zero,if_false]
      rw [← Int.natCast_ediv,truncate_nat]
      simp only [Operation.result,zero,if_false] at written
      rw [run_bind_of_ok _ _ _ _ _ written]
      rfl
  · simp only [clause,SailRV32.Functions.execute_REM]
    rw [run_bind_of_ok _ _ _ _ _ leftRead,run_bind_of_ok _ _ _ _ _ rightRead]
    simp [_root_.Sail.BitVec.toNatInt,Word.toBitVec_toNat leftBound,Word.toBitVec_toNat rightBound]
    by_cases zero : right.value = 0
    · simp only [zero,if_true]
      rw [truncate_nat]
      simp only [Operation.result,zero,Nat.mod_zero] at written
      rw [run_bind_of_ok _ _ _ _ _ written]
      rfl
    · simp only [zero,if_false]
      rw [← Int.ofNat_tmod,truncate_nat]
      simp only [Operation.result] at written
      rw [run_bind_of_ok _ _ _ _ _ written]
      rfl

/-- Native results and actual masked writes execute the original clause.
    Destination aliases and original x0 instructions are retained. -/
theorem native_clause {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (leftBound : (left w).Bounded)
    {before after : State}
    (transfer : RegisterTransfer (⟨.mulDiv,w⟩ : Row mersenne31Modulus MulDivFamily) entry before after) :
    run (clause entry.data.family entry.data.rs1 entry.data.rs2 entry.data.rd) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have result := native_result holds entry.data.family (query_mask (by decide) fields query) leftBound
  have rightBound := (byte_words holds).2.1
  have leftRead := transfer.1 ⟨0,by decide⟩
  have rightRead := transfer.1 ⟨1,by decide⟩
  have written := transfer.2
  simp only [importedConstraintsMemoryPorts,MemoryPort.readCode,MemoryPort.writeCode,
    WordColumns.code,WordColumns.evaluate,memoryWord,Nat.unpair_pair] at leftRead rightRead written
  have leftActual : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (left w).toBitVec before := by simpa [left,Word.toBitVec,Word.value,pairCode] using leftRead
  have rightActual : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (right w).toBitVec before := by simpa [right,Word.toBitVec,Word.value,pairCode] using rightRead
  have writeActual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (writtenWord w).toBitVec) before = .ok () after := by
    simpa [writtenWord,Word.toBitVec,Word.value,pairCode] using written
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
  change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (BitVec.ofNat 32 (entry.data.family.result (left w) (right w)))) before = .ok () after := by
    by_cases zero : entry.data.rd = 0
    · rw [zero] at writeActual ⊢
      change run (SailRV32.Functions.wX_bits zeroRegister _) before = _ at writeActual ⊢
      rw [write_zero] at writeActual ⊢
      exact writeActual
    · rw [if_neg zero] at flag
      have mask := written_mask holds false flag
      rw [mask] at writeActual
      change run (SailRV32.Functions.wX_bits _ (BitVec.ofNat 32 (selectedWord w).value)) before = _ at writeActual
      rw [result] at writeActual
      exact writeActual
  exact clause_of_reads _ _ _ _ _ _ leftBound rightBound leftActual rightActual actual

end Airbender.MulDiv.Proofs
