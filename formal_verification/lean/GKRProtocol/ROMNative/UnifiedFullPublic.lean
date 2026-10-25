import GKRProtocol.ROMNative.UnifiedBoundary
import Airbender.Proofs.UnifiedReduced.Tables.ImportedROM
import GKRProtocol.CleanClosedNative.UnifiedUncached
import GKRProtocol.CleanClosedNative.UnifiedCached

namespace Airbender.Compiler.ROMNative.UnifiedFullPublic
open Airbender Airbender.Compiler
set_option warningAsError true

/-- Full native non-decoder queries refine the retained table fixed by the
public byte image. Decoder queries keep their distinct program interface. -/
theorem public_table_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 10}
    (member : (UnifiedBoundary.nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] query)
    (notDecoder : query[9] ≠ 46) :
    (UnifiedReduced.Setup.table (p := babyBearModulus) before).Contains #[] query := by
  rw [← UnifiedReduced.Setup.Proofs.imported_table_before image]
  exact UnifiedBoundary.full_table_refinement member notDecoder

theorem uncached_public_table_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 10}
    (member : Airbender.Compiler.CleanClosedNative.UnifiedUncached.nativeSetup.Contains #[] query)
    (notDecoder : query[9] ≠ 46) :
    (UnifiedReduced.Setup.table (p := babyBearModulus) before).Contains #[] query :=
  public_table_refinement image member notDecoder

theorem cached_public_table_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 10}
    (member : Airbender.Compiler.CleanClosedNative.UnifiedCached.nativeSetup.Contains #[] query)
    (notDecoder : query[9] ≠ 46) :
    (UnifiedReduced.Setup.table (p := babyBearModulus) before).Contains #[] query :=
  public_table_refinement image member notDecoder

end Airbender.Compiler.ROMNative.UnifiedFullPublic
