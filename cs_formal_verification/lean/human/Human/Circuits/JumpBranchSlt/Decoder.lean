module
public import Human.Helpers.Decoder.Program
public import Human.Circuits.JumpBranchSlt.Artifact

@[expose] public section

namespace Airbender.JumpBranchSlt
open Arithmetic

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.JumpBranchSlt
