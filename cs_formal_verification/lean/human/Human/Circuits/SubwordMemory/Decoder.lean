import Human.Circuits.SubwordMemory.Artifact
import Human.Helpers.Decoder.Program

namespace Airbender.SubwordMemory
open Arithmetic

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.SubwordMemory
