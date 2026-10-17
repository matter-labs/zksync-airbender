import Airbender.Review.Helpers.Decoder.ImportedUnified
import Airbender.Proofs.Tables.Decoder.Unified
import Airbender.Proofs.Tables.DecoderPCLow

namespace Airbender.Trace.NativeDecoder.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Accepted constraints and raw state matching derive the guarded limb;
    actual imported membership then gives original Sail metadata. -/
theorem unified_decoded [Fact p.Prime] (hp : 65536 < p) {trace : UnifiedTrace p}
    (accepted : Accepted trace) (initial : trace.initial.word.lo < Arithmetic.limbBase)
    (lookups : UnifiedLookups trace) : UnifiedReduced.Decoded trace unifiedProgram := by
  intro row member
  exact Unified.lookup_sound hp row.decoderQuery
    (unified_query_pc_low accepted initial row member) (lookups row member)

end Airbender.Trace.NativeDecoder.Proofs
