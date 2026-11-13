module
public import Proven.Trace.RVPooled.Row
public import Proven.UnifiedReduced.RV.Row
public import Mathlib.Data.Nat.Bitwise

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true

/-- An ordinary pooled arithmetic entry has only the reviewed low arithmetic bits. -/
theorem pooled_arithmetic_mask_bound {instruction : RV.Instr} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields instruction = some data) (family : data.family = .addSub) : data.mask ≤ 4 := by
  obtain ⟨ordinary, projected, same⟩ := (rv_pooled_fields_family fields).1 (Or.inl family)
  rw [same]
  exact (rv_decoder_field_bounds projected).2

/-- Ordinary unified metadata selects neither a delegation caller nor an external input read. -/
theorem unified_ordinary_mask_bits {instruction : RV.Instr} {data : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.rvDecoderFields instruction = some data) :
    data.mask.testBit 7 = false ∧ data.mask.testBit 8 = false := by
  rcases UnifiedReduced.Proofs.RV.rv_fields_cases fields with ⟨_, rfl⟩ | ⟨_, word⟩ | ⟨_, _, jump, _, rfl⟩ |
      ⟨_, _, _, binary, _, rfl⟩ | ⟨_, _, _, _, custom⟩
  · change Nat.testBit 1 7 = false ∧ Nat.testBit 1 8 = false
    decide
  · obtain ⟨_, masks, _⟩ := UnifiedReduced.Proofs.RV.rv_word_fields_bounds word
    rcases masks with mask | mask | mask | mask | mask <;> rw [mask] <;> decide
  · change (1024 * jump.mask).testBit 7 = false ∧ (1024 * jump.mask).testBit 8 = false
    rw [show (1024 : Nat) = 2 ^ 10 by decide, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul]
    exact ⟨rfl, rfl⟩
  · change (32768 * binary.mask).testBit 7 = false ∧ (32768 * binary.mask).testBit 8 = false
    rw [show (32768 : Nat) = 2 ^ 15 by decide, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul]
    exact ⟨rfl, rfl⟩
  · obtain ⟨_, masks, _⟩ := UnifiedReduced.Proofs.RV.rv_custom_fields_bounds custom
    rcases masks with mask | mask <;> rw [mask] <;> decide

/-- The ordinary unified decoder never admits an external-input instruction. -/
theorem unified_ordinary_no_read {instruction : RV.Instr} {data : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.rvDecoderFields instruction = some data) : instruction.readsInput = false := by
  cases instruction <;> try rfl
  case inputRead rd =>
    have rejected : UnifiedReduced.rvDecoderFields (.inputRead rd) = none := rfl
    rw [rejected] at fields
    cases fields

end Airbender.Trace.Machine.Proofs
