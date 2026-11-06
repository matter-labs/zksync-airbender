import Slop.Trace.ZeroValues
import Slop.Trace.Program
import Slop.Trace.Values

namespace Airbender.Trace.Proofs
open Arithmetic

private theorem arithmetic_zero_fields (rs1 rs2 rd : BitVec 5) (bits : BitVec 32) (mask : Nat)
    (zero : (arithmeticFields rs1 rs2 rd bits mask).rd = 0) :
    arithmeticFields rs1 rs2 rd bits mask = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  unfold arithmeticFields at *
  split at zero <;> simp_all

private theorem arithmetic_family (rs1 rs2 rd : BitVec 5) (bits : BitVec 32) (mask : Nat) :
    (arithmeticFields rs1 rs2 rd bits mask).family = .addSub := by
  unfold arithmeticFields
  split <;> rfl

/-- The retained native decoder projection turns every selected arithmetic
    write to x0 (including a discarded LW) into the same zero-operand ADD row. -/
theorem decoder_zero_nop {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : decoderFields instruction = some data) (family : data.family = .addSub)
    (zero : data.rd = 0) : data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  unfold decoderFields at fields
  split at fields
  case h_6 =>
    rename_i original imm rs1 rd
    change (if (rd : BitVec 5) = 0 then some (arithmeticFields 0 0 0 0 1)
      else some ⟨.wordMemory, rs1, 0, rd,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) = some data at fields
    by_cases discarded : (rd : BitVec 5) = 0
    · rw [ite_eq_left discarded, Option.some.injEq] at fields
      subst data
      rfl
    · rw [ite_eq_right discarded, Option.some.injEq] at fields
      subst data
      cases family
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       exact arithmetic_zero_fields _ _ _ _ _ zero)
    | (simp only [Option.some.injEq] at fields
       subst data
       cases family)
    | cases fields

theorem decoder_load_nonzero {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : decoderFields instruction = some data) (family : data.family = .wordMemory)
    (load : data.mask = 0) : data.rd ≠ 0 := by
  unfold decoderFields at fields
  split at fields
  case h_6 =>
    rename_i original imm rs1 rd
    change (if (rd : BitVec 5) = 0 then some (arithmeticFields 0 0 0 0 1)
      else some ⟨.wordMemory, rs1, 0, rd,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) = some data at fields
    by_cases discarded : (rd : BitVec 5) = 0
    · rw [ite_eq_left discarded, Option.some.injEq] at fields
      subst data
      cases family
    · rw [ite_eq_right discarded, Option.some.injEq] at fields
      subst data
      exact discarded
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       have impossible : Family.addSub = .wordMemory := by
         simpa only [arithmetic_family] using family
       cases impossible)
    | (simp only [Option.some.injEq] at fields
       subst data
       change 1 = 0 at load
       cases load)
    | cases fields

/-- Proof-only metadata facts needed by the shared native x0/history argument.
    These are proved for each projection, not assumed by the public trace claim. -/
structure DecoderRules (projection : SailRV32.instruction → Option DecoderData) : Prop where
  bounds : ∀ instruction data, projection instruction = some data →
    data.immediate.Bounded ∧ data.mask < 512
  zeroNop : ∀ instruction data, projection instruction = some data →
    data.family = .addSub → data.rd = 0 → data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
  loadNonzero : ∀ instruction data, projection instruction = some data →
    data.family = .wordMemory → data.mask = 0 → data.rd ≠ 0

def standardDecoderRules : DecoderRules decoderFields where
  bounds instruction data fields := by
    have bound := decoder_field_bounds fields
    exact ⟨bound.1, by omega⟩
  zeroNop _ _ := decoder_zero_nop
  loadNonzero _ _ := decoder_load_nonzero

end Airbender.Trace.Proofs
