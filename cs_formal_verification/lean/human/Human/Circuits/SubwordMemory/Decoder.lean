module
public import Human.Circuits.SubwordMemory.Artifact
public import Human.Helpers.Decoder.Program

@[expose] public section

namespace Airbender.SubwordMemory
open Arithmetic

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.SubwordMemory
