import Airbender.Review.Helpers.Tables.NativeDecoder
import Airbender.Proofs.AddSub.ArtifactChecks
import Airbender.Proofs.WordMemory.ArtifactChecks

namespace Tests.NativeDecoderRows
open Airbender Verification NativeSetup

theorem compiled_geometry :
    AddSub.importedConstraintsSetupColumns.traceLength = 16777216 ∧
    AddSub.importedConstraintsSetupColumns.decoderStart = 2 ∧
    AddSub.importedConstraintsSetupColumns.decoderCapacity = 1048576 ∧
    WordMemory.importedConstraintsSetupColumns.traceLength = 16777216 ∧
    WordMemory.importedConstraintsSetupColumns.decoderStart = 6 ∧
    WordMemory.importedConstraintsSetupColumns.decoderCapacity = 1048576 ∧
    Fintype.card Row = 16777215 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact Fintype.card_fin _

theorem native_padding : decoderPadding = Vector.replicate 10 2147483646 := by decide +kernel

/-- Real supported rows survive the active model, with their original indexed PCs. -/
theorem supported_prefix :
    decoderRow .arithmetic ⟨6, by decide⟩ = #v[24,0,1,1,1,0,0,0,0,1] ∧
    decoderRow .wordMemory ⟨0, by decide⟩ = #v[0,0,1,0,3,0,16,0,2,0] ∧
    decoderRow .wordMemoryHoles ⟨3, by decide⟩ = #v[12,0,1,0,0,1,16,0,2,0] := by decide +kernel

theorem active_boundaries (kind : DecoderKind) :
    decoderRow kind ⟨1048576, by decide⟩ = Vector.replicate 10 (-1) ∧
    decoderRow kind ⟨16777214, by decide⟩ = Vector.replicate 10 (-1) :=
  ⟨NativeSetup.Proofs.decoder_active_tail _ _ (by decide),
    NativeSetup.Proofs.decoder_active_tail _ _ (by decide)⟩

theorem padding_retained (kind : DecoderKind) :
    DecoderContains kind (Vector.replicate 10 (-1)) :=
  ⟨⟨16777214, by decide⟩, (NativeSetup.Proofs.decoder_active_tail _ _ (by decide)).symm⟩

/-- Source comments mentioning zero padding do not replace actual native data. -/
theorem tail_is_not_zero (kind : DecoderKind) :
    decoderRow kind ⟨16777214, by decide⟩ ≠ Vector.replicate 10 0 := by
  rw [NativeSetup.Proofs.decoder_active_tail _ _ (by decide)]
  decide +kernel

end Tests.NativeDecoderRows
