module
public import Human.Helpers.Decoder.Program
public import Human.Circuits.MulDiv.Artifact

@[expose] public section

namespace Airbender.MulDiv
open Arithmetic

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.MulDiv
