import Human.Helpers.Decoder.Program
import Human.Circuits.JumpBranchSlt.Artifact

namespace Airbender.JumpBranchSlt
open Arithmetic

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.JumpBranchSlt
