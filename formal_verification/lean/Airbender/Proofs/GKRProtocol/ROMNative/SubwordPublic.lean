import Airbender.Proofs.GKRProtocol.ROMNative.SubwordBoundary
import Airbender.Proofs.Tables.ImportedSubwordROM
import Airbender.Proofs.GKRProtocol.CleanClosedNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanClosedNative.SubwordMemoryCached

namespace Airbender.Compiler.ROMNative.SubwordPublic
open Airbender Airbender.Compiler
set_option warningAsError true

/-- Full native non-decoder queries refine the retained table fixed by the
public byte image. Decoder queries keep their distinct program interface. -/
theorem public_table_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 9}
    (member : (SubwordBoundary.nativeSetup.imported.data.table "Airbender.Native.SubwordMemory").Contains #[] query)
    (notDecoder : query[8] ≠ 46) :
    (Verification.subwordTable (p := babyBearModulus) (Trace.ROM.words before)).Contains #[] query := by
  rw [← Verification.SubwordROMGeometry.imported_subword_table_before image]
  exact SubwordBoundary.full_table_refinement member notDecoder

theorem uncached_public_table_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 9}
    (member : Airbender.Compiler.CleanClosedNative.SubwordMemoryUncached.nativeSetup.Contains #[] query)
    (notDecoder : query[8] ≠ 46) :
    (Verification.subwordTable (p := babyBearModulus) (Trace.ROM.words before)).Contains #[] query :=
  public_table_refinement image member notDecoder

theorem cached_public_table_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 9}
    (member : Airbender.Compiler.CleanClosedNative.SubwordMemoryCached.nativeSetup.Contains #[] query)
    (notDecoder : query[8] ≠ 46) :
    (Verification.subwordTable (p := babyBearModulus) (Trace.ROM.words before)).Contains #[] query :=
  public_table_refinement image member notDecoder

end Airbender.Compiler.ROMNative.SubwordPublic
