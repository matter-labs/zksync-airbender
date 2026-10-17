import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Helpers.Decoder.SetupData.AddSub
import Airbender.Review.Helpers.Decoder.SetupData.JumpBranch
import Airbender.Review.Helpers.Decoder.SetupData.MulDiv
import Airbender.Review.Helpers.Decoder.SetupData.ShiftBinop
import Airbender.Review.Helpers.Decoder.SetupData.WordMemory
import Airbender.Review.Helpers.Decoder.SetupData.Subword

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
