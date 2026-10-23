import Airbender.Proofs.UnifiedReduced.ArithmeticExecution

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem arithmetic_index {input : Input} {entry : ProgramEntry} {w : Nat → ZMod p}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = arithmeticInstruction input) (query : decoderQuery w = entry.query) :
    match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p) := by
  have index := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod p) at index
  rw [encoding] at fields
  rcases input with ⟨⟨op, left, right, immediate, pc⟩, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, imm, upper, state⟩
  change BitVec 5 at rs1 rs2 rd
  cases op <;> by_cases zero : rd = (0#5)
  all_goals simp [arithmeticInstruction, Sail.instruction, decoderFields, Trace.decoderFields, arithmeticFields,
    Trace.arithmeticFields, DecoderData.mapFamily, zero] at fields
  all_goals rw [← fields] at index
  all_goals simpa [zero] using index

end Airbender.UnifiedReduced.Proofs
