import Airbender.Review.Helpers.UnifiedReduced.Registry
import Airbender.Review.Helpers.Decoder.Program
import Airbender.Data.Decoder.Setup.Unified

namespace Airbender.Trace.NativeDecoder

/-- Full physical decoder setup for the selected unified program. -/
def UnifiedLookups {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p) : Prop :=
  ∀ row ∈ trace.rows, unifiedSetup.lookup row.decoderQuery

end Airbender.Trace.NativeDecoder
