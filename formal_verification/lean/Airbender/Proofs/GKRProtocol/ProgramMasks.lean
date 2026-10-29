import Airbender.Review.Helpers.Decoder.ProgramRows
import Airbender.Data.Decoder.Setup.AddSub
import Airbender.Data.Decoder.Setup.JumpBranch
import Airbender.Data.Decoder.Setup.ShiftBinop
import Airbender.Data.Decoder.Setup.WordMemory
import Airbender.Data.Decoder.Setup.Subword
import Airbender.Data.Decoder.Setup.MulDiv
import Airbender.Data.Decoder.Setup.Unified

namespace Airbender.Trace.NativeDecoder.ProgramRows.Proofs
open Airbender.Trace.NativeDecoder.ProgramRows

/-- The masks come from the imported native setup metadata, not a second
handwritten copy. This selects the decoder setup of the six unrolled families;
it does not assert that its captured rows equal the public-text row model. -/
def setupOfFamily : PooledFamily → PackedSetup
  | .addSub => addSubSetup
  | .jumpBranchSlt => jumpBranchSetup
  | .shiftBinop => shiftBinopSetup
  | .wordMemory => wordMemorySetup
  | .subwordMemory => subwordSetup
  | .mulDiv => mulDivSetup

def maskOfFamily (family : PooledFamily) : Mask := {
  columns := (setupOfFamily family).columnsMask
  width := by cases family <;> decide
  pcLow := by cases family <;> decide
  pcHigh := by cases family <;> decide
}

/-- Unified has a separate native decoder mask. Its program-row projection
needs the unified Rust decoder and is not supplied by the pooled model. -/
def unifiedMask : Mask := {
  columns := unifiedSetup.columnsMask
  width := by decide
  pcLow := by decide
  pcHigh := by decide
}

end Airbender.Trace.NativeDecoder.ProgramRows.Proofs
