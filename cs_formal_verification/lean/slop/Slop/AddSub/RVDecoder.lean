import Human.Circuits.AddSub.RVModel
import Slop.Trace.RVProgram

/-! Native decoder metadata of the RV AddSub row's instruction: `rvDecoderFields (rvInstruction input)` is, per opcode,
    `arithmeticFields` of the RV fields. -/

namespace Airbender.AddSub.Proofs
open Arithmetic Trace

/-- The decoder data of `rvInstruction input` (`rvDecoderFields`). -/
def rvData (input : RVInput) : DecoderData :=
  match input.row.opcode with
  | .add => arithmeticFields input.rs1 input.rs2 input.rd 0 1
  | .addi => arithmeticFields input.rs1 0 input.rd (input.encodedImmediate.signExtend 32) 1
  | .sub => arithmeticFields input.rs1 input.rs2 input.rd 0 2
  | .lui => arithmeticFields 0 0 input.rd (input.encodedUpperImmediate ++ 0#12) 1
  | .auipc => arithmeticFields 0 0 input.rd (input.encodedUpperImmediate ++ 0#12) 4

theorem rv_decoder_fields (input : RVInput) :
    rvDecoderFields (rvInstruction input) = some (rvData input) := by
  obtain ⟨⟨opcode, _, _, _, _⟩, rs1, rs2, rd, e, u, _⟩ := input
  cases opcode <;> rfl

theorem rv_pooled_fields (input : RVInput) :
    rvPooledDecoderFields (rvInstruction input) =
      some ((rvData input).mapFamily pooledArithmeticFamily) := by
  unfold rvPooledDecoderFields
  rw [rv_decoder_fields]
  rfl

end Airbender.AddSub.Proofs
