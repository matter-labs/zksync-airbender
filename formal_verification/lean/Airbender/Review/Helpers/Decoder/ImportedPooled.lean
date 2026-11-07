import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Data.Decoder.Setup.AddSub
import Airbender.Data.Decoder.Setup.JumpBranch
import Airbender.Data.Decoder.Setup.MulDiv
import Airbender.Data.Decoder.Setup.ShiftBinop
import Airbender.Data.Decoder.Setup.WordMemory
import Airbender.Data.Decoder.Setup.Subword

namespace Airbender.Trace.NativeDecoder

def pooledSetup : PooledFamily → PackedSetup
  | .addSub => addSubSetup
  | .jumpBranchSlt => jumpBranchSetup
  | .mulDiv => mulDivSetup
  | .shiftBinop => shiftBinopSetup
  | .wordMemory => wordMemorySetup
  | .subwordMemory => subwordSetup

/-- Actual imported full-domain decoder membership, including native omitted
    columns, discriminators, unsupported slots and committed padding. -/
def PooledLookups {p : Nat} [Fact p.Prime] (trace : PooledTrace p) : Prop :=
  ∀ row ∈ trace.rows,
    (pooledSetup row.family).lookup row.decoderQuery

end Airbender.Trace.NativeDecoder
