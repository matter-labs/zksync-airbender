import Human.Helpers.Decoder.Program
import Human.Circuits.MulDiv.Artifact

namespace Airbender.MulDiv
open Arithmetic

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.MulDiv
