import GKRProtocol.ROMNative.UnifiedFullPublic

namespace Tests.GKRUnifiedFullNative
open Airbender Airbender.Compiler
open Airbender.Compiler.ROMNative
set_option warningAsError true

theorem native_rom_starts_before_rotations :
    UnifiedRows.nativeRow ⟨590081, by decide⟩ =
      (UnifiedReduced.Setup.importedRow ⟨1048961, by decide⟩).map (fun n : Nat => (n : Source.BaseField)) :=
  UnifiedRows.region7_retained ⟨0, by decide⟩

theorem native_rotation_moves_before_rom :
    UnifiedRows.nativeRow ⟨1638657, by decide⟩ =
      (UnifiedReduced.Setup.importedRow ⟨786817, by decide⟩).map (fun n : Nat => (n : Source.BaseField)) :=
  UnifiedRows.region8_retained ⟨0, by decide⟩

theorem decoder_keeps_distinct_tag :
    UnifiedBoundary.nativeSetup.value ⟨2097537, by decide⟩ (.generic 9) = 46 :=
  UnifiedBoundary.decoder_tag _ (by decide) (by decide)

theorem committed_padding_is_disabled :
    UnifiedRows.nativeRow ⟨3146113, by decide⟩ = Vector.replicate 10 0 :=
  UnifiedBoundary.padding_row _ (by decide)

end Tests.GKRUnifiedFullNative
