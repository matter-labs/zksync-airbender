import Airbender.Review.Trace.Pooled
import Airbender.Review.Trace.Program
import Airbender.Review.JumpBranchSlt.Decoder
import Airbender.Review.MulDiv.Decoder
import Airbender.Review.ShiftBinop.Decoder
import Airbender.Review.SubwordMemory.Decoder

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

abbrev pooledProgramImage := programImageRunWith pooledDecoderFields
abbrev PooledProgramEntry := ProgramEntry PooledFamily

def PooledDecoded {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (program : List PooledProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program row.family).Contains #[] row.decoderQuery

end Airbender.Trace
