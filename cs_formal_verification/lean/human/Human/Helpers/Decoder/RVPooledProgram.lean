module
public import Human.Helpers.Decoder.PooledProgram
public import Human.Circuits.JumpBranchSlt.RVDecoder
public import Human.Circuits.MulDiv.RVDecoder
public import Human.Circuits.ShiftBinop.RVDecoder
public import Human.Circuits.SubwordMemory.RVDecoder

@[expose] public section

namespace Airbender.Trace

/-- The six-family registry's metadata projection on `RV.Instr` (as `pooledDecoderFields`): whichever admitted
    family's native decoder applies. -/
def rvPooledDecoderFields (i : RV.Instr) : Option (DecoderData PooledFamily) :=
  (rvDecoderFields i).map (DecoderData.mapFamily pooledArithmeticFamily) <|>
  (JumpBranchSlt.rvDecoderFields i).map (DecoderData.mapFamily fun _ => .jumpBranchSlt) <|>
  (MulDiv.rvDecoderFields i).map (DecoderData.mapFamily fun _ => .mulDiv) <|>
  (ShiftBinop.rvDecoderFields i).map (DecoderData.mapFamily fun _ => .shiftBinop) <|>
  (SubwordMemory.rvDecoderFields i).map (DecoderData.mapFamily fun _ => .subwordMemory)

abbrev RVPooledProgramEntry := RVProgramEntry PooledFamily

/-- Decoder lookup membership for every row of the six-family trace, in the RV table. Public
    image binding is separate (`RVNativeInputs.programImage`). Logical membership; lookup enforcement is deferred. -/
def RVPooledDecoded {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (program : List RVPooledProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program row.family).Contains #[] row.decoderQuery

end Airbender.Trace
