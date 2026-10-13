import Airbender.Review.Helpers.Pooled
import Airbender.Review.Helpers.Program
import Airbender.Review.Circuits.JumpBranchSlt.Decoder
import Airbender.Review.Circuits.MulDiv.Decoder
import Airbender.Review.Circuits.ShiftBinop.Decoder
import Airbender.Review.Circuits.SubwordMemory.Decoder

namespace Airbender.Trace

def pooledArithmeticFamily : Family → PooledFamily
  | .addSub => .addSub
  | .wordMemory => .wordMemory

/-- Reuse the existing native metadata projections. This registry selects a
    layout; instruction decoding and execution still come from pinned Sail. -/
def pooledDecoderFields (instruction : SailRV32.instruction) : Option (DecoderData PooledFamily) :=
  (decoderFields instruction).map (DecoderData.mapFamily pooledArithmeticFamily) <|>
  (JumpBranchSlt.decoderFields instruction).map (DecoderData.mapFamily fun _ => .jumpBranchSlt) <|>
  (MulDiv.decoderFields instruction).map (DecoderData.mapFamily fun _ => .mulDiv) <|>
  (ShiftBinop.decoderFields instruction).map (DecoderData.mapFamily fun _ => .shiftBinop) <|>
  (SubwordMemory.decoderFields instruction).map (DecoderData.mapFamily fun _ => .subwordMemory)

/-- Read public bytes and run pinned Sail decoding, retaining the original
    instruction and whichever admitted family's native metadata applies. -/
abbrev pooledProgramImage := programImageRunWith pooledDecoderFields
abbrev PooledProgramEntry := ProgramEntry PooledFamily

/-- Decoder lookup membership for every participating row in the six-family
    trace. Public image binding is separate: `NativeInputs.programImage` or
    `PooledBootInputs.programImage` constructs `program` from actual Sail decoding.
    This is logical membership; cryptographic lookup enforcement is deferred. -/
def PooledDecoded {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (program : List PooledProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program row.family).Contains #[] row.decoderQuery

end Airbender.Trace
