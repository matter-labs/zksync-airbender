import Airbender.Review.Circuits.AddSub.Artifact
import Airbender.Review.Helpers.Decoder.NativeData

namespace Tests.NativeDecoderMetadata
open Airbender

/-- Mechanical native flatten order: rd_is_zero is column five, separate from mask. -/
theorem query_order {p : Nat} (w : Nat → ZMod p) :
    Trace.nativeDecoderQuery AddSub.importedConstraintsTraceColumns
      AddSub.importedConstraintsDecoderColumns w =
      #v[w 0, w 1, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12] := rfl

end Tests.NativeDecoderMetadata
