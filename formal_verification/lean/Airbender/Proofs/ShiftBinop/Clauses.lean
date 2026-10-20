import Airbender.Proofs.ShiftBinop.Results
import Airbender.Proofs.ShiftBinop.Routing
import Airbender.Review.Helpers.Memory.ShiftBinop
import Airbender.Proofs.Sail.PC

namespace Airbender.ShiftBinop.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification

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
    ((amount.setWidth 32).extractLsb' 0 5).toNat = (amount.extractLsb' 0 5).toNat := by
  simp

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
theorem decoded_clause_of_reads {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    {before after : State} (left operand registerRight : Word)
    (leftRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok left.toBitVec before)
    (rightRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok registerRight.toBitVec before)
    (selected : operand = if 32 ≤ entry.data.mask then entry.data.immediate else registerRight)
    (written : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (entry.data.family.result left operand)) before = .ok () after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [instructionFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       rw [← fields] at leftRead rightRead selected written
       simp_all only [registerClause]
       refine ⟨_,rfl,?_⟩
       norm_num [Operation.mask] at selected written
       try subst operand
       simp only [SailRV32.Functions.execute_RTYPE,SailRV32.Functions.execute_ITYPE,
         SailRV32.Functions.execute_SHIFTIOP,freeM_bind_assoc,freeM_pure_bind]
       rw [run_bind_of_ok _ _ _ _ _ leftRead]
       try rw [run_bind_of_ok _ _ _ _ _ rightRead]
       simp only [Operation.result,ShiftKind.result] at written
       try simp only [sail_shift_left,sail_shift_right,sail_shift_arithmetic]
       try simp only [Word.ofBitVec_roundtrip] at written
       try rw [extended_amount] at written
       try rw [encoded_arithmetic_amount] at written
       rw [run_bind_of_ok _ _ _ _ _ written]
       rfl)

/-- Accepted native routing and the actual public immediate columns determine
    the complete selected operand, including SRAI's retained funct7 bits. -/
theorem entry_selected_operand {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    right w = if 32 ≤ entry.data.mask then entry.data.immediate else
      (⟨(w 25).val,(w 26).val⟩ : Word) := by
  have routed := entry_routing native fields query
  have bounds := (decoder_field_bounds fields).1
  have low := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[6]) query
  have high := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[7]) query
  change w 9 = (entry.data.immediate.lo : ZMod mersenne31Modulus) at low
  change w 10 = (entry.data.immediate.hi : ZMod mersenne31Modulus) at high
  have small : limbBase < mersenne31Modulus := by decide
  by_cases immediate : 32 ≤ entry.data.mask
  · simp only [if_pos immediate] at routed ⊢
    apply congrArg₂ Word.mk
    · change (w 27).val = entry.data.immediate.lo
      rw [routed.operandLow,if_pos immediate,low,ZMod.val_natCast_of_lt (lt_trans bounds.1 small)]
    · change (w 28).val = entry.data.immediate.hi
      rw [routed.operandHigh,if_pos immediate,high,ZMod.val_natCast_of_lt (lt_trans bounds.2 small)]
  · simp only [if_neg immediate]
    apply congrArg₂ Word.mk
    · rw [routed.operandLow,if_neg immediate]
    · rw [routed.operandHigh,if_neg immediate]

/-- Original decoding, accepted constraints and actual native GPR transfers
    execute the original clause into the same actual after-state. Bounds are
    supplied internally by initialized history at the public theorem. -/
theorem native_clause {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (left w).Bounded)
    {before after : State}
    (transfer : RegisterTransfer (⟨.shiftBinop,w⟩ : Row mersenne31Modulus ShiftBinopFamily)
      entry before after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have result := (entry_numerical_result native fields query source).2
  have leftRead := transfer.1 ⟨0,by decide⟩
  have rightRead := transfer.1 ⟨1,by decide⟩
  have written := transfer.2
  simp only [importedConstraintsMemoryPorts,MemoryPort.readCode,MemoryPort.writeCode,
    WordColumns.code,WordColumns.evaluate,memoryWord,Nat.unpair_pair] at leftRead rightRead written
  have leftActual : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (left w).toBitVec before := by
    simpa [left,Word.toBitVec,Word.value,pairCode] using leftRead
  have rightActual : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (⟨(w 25).val,(w 26).val⟩ : Word).toBitVec before := by
    simpa [Word.toBitVec,Word.value,pairCode] using rightRead
  have writeActual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (writtenWord w).toBitVec) before = .ok () after := by
    simpa [writtenWord,Word.toBitVec,Word.value,pairCode] using written
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (entry.data.family.result (left w) (right w))) before = .ok () after := by
    by_cases zero : entry.data.rd = 0
    · rw [zero] at writeActual ⊢
      change run (SailRV32.Functions.wX_bits zeroRegister _) before = _ at writeActual ⊢
      rw [write_zero] at writeActual ⊢
      exact writeActual
    · rw [result,if_neg zero,Word.ofBitVec_roundtrip] at writeActual
      exact writeActual
  exact decoded_clause_of_reads fields _ _ _ leftActual rightActual
    (entry_selected_operand native fields query) actual

end Airbender.ShiftBinop.Proofs
