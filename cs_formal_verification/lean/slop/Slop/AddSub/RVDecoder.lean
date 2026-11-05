import Human.Circuits.AddSub.RVModel
import Slop.Trace.PooledProgram

/-! Native decoder metadata of the RV AddSub row's instruction. `decoderFields (toSail i)` is a function of the
    instruction datatype (no Sail interpreter): per opcode it is `arithmeticFields` of the RV fields. -/

namespace Airbender.AddSub.Proofs
open Arithmetic Trace

/-- The decoder data of `rvInstruction input` (`decoderFields` after `toSail`). -/
def rvData (input : RVInput) : DecoderData :=
  match input.row.opcode with
  | .add => arithmeticFields input.rs1 input.rs2 input.rd 0 1
  | .addi => arithmeticFields input.rs1 0 input.rd (input.encodedImmediate.signExtend 32) 1
  | .sub => arithmeticFields input.rs1 input.rs2 input.rd 0 2
  | .lui => arithmeticFields 0 0 input.rd (input.encodedUpperImmediate ++ 0#12) 1
  | .auipc => arithmeticFields 0 0 input.rd (input.encodedUpperImmediate ++ 0#12) 4

private theorem sext12_low (x : BitVec 12) :
    SailRV32.Functions.sign_extend (m := 32) ((x.signExtend 32).extractLsb' 0 12) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [SailRV32.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_extractLsb']
  by_cases h : j < 12 <;> simp [h, hj, BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD,
    BitVec.getElem_signExtend]

private theorem upper_low (u : BitVec 20) : (u ++ 0#12).extractLsb' 12 20 = u := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [hj]
  rw [BitVec.getLsbD_append]
  simp [BitVec.getLsbD_eq_getElem hj]

theorem rv_decoder_fields (input : RVInput) :
    decoderFields (Airbender.toSail (rvInstruction input)) = some (rvData input) := by
  obtain ⟨⟨opcode, _, _, _, _⟩, rs1, rs2, rd, e, u, _⟩ := input
  cases opcode
  · rfl
  · change decoderFields (.ITYPE ((e.signExtend 32).extractLsb' 0 12, .Regidx rs1, .Regidx rd, .ADDI)) = _
    simp only [decoderFields, sext12_low]
    rfl
  · rfl
  · change decoderFields (.UTYPE ((u ++ 0#12).extractLsb' 12 20, .Regidx rd, .LUI)) = _
    simp only [decoderFields, upper_low]
    rfl
  · change decoderFields (.UTYPE ((u ++ 0#12).extractLsb' 12 20, .Regidx rd, .AUIPC)) = _
    simp only [decoderFields, upper_low]
    rfl

theorem rv_pooled_fields (input : RVInput) :
    pooledDecoderFields (Airbender.toSail (rvInstruction input)) =
      some ((rvData input).mapFamily pooledArithmeticFamily) := by
  unfold pooledDecoderFields
  rw [rv_decoder_fields]
  rfl

end Airbender.AddSub.Proofs
