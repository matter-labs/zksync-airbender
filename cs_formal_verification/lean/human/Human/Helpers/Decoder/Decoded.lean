import Human.Helpers.Context.FamilyLayout
import Human.Helpers.Decoder.Program

-- As in `Program.lean`: specifications read by proofs, never executed.
noncomputable section

namespace Airbender.Trace
open Arithmetic

/-- Each native row's imported decoder query belongs to its family's modeled
    program table. `program` must separately be bound to public bytes by image
    construction. Together these let the proofs recover its original Sail
    instruction and selector choices. Lookup-argument enforcement remains external. -/
def Decoded [Fact p.Prime] (trace : Data p) (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program row.family).Contains #[] row.decoderQuery

/-- The imported query agrees with an actual fetched/decoded public instruction
    at this row's PC, including its indices, immediate and each selector bit. -/
def Row.Fetched (row : Row p) (before : Reference.RiscV.Sail.State)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop :=
  ∃ entry : ProgramEntry, entry.Source before projection ∧ entry.data.family = row.family ∧
    row.decoderQuery = entry.query ∧ row.start.word.toBitVec = entry.pc ∧
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

end Airbender.Trace
