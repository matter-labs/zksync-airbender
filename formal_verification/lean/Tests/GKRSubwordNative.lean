import GKRProtocol.ROMNative.SubwordPublic

namespace Tests.GKRSubwordNative
open Airbender Airbender.Compiler
open Airbender.Compiler.ROMNative
set_option warningAsError true

theorem half_rom_tag :
    SubwordBoundary.nativeSetup.value ⟨655361, by decide⟩ (.generic 8) = 44 := by
  rw [SubwordBoundary.nativeSetup.generic_cell_value _ (⟨8, by decide⟩ : Fin 9)]
  decide +kernel

theorem byte_rom_tag :
    SubwordBoundary.nativeSetup.value ⟨4849665, by decide⟩ (.generic 8) = 45 := by
  rw [SubwordBoundary.nativeSetup.generic_cell_value _ (⟨8, by decide⟩ : Fin 9)]
  decide +kernel

theorem decoder_keeps_distinct_tag :
    SubwordBoundary.nativeSetup.value ⟨13238273, by decide⟩ (.generic 8) = 46 :=
  SubwordBoundary.decoder_tag _ (by decide) (by decide)

theorem committed_padding_is_disabled :
    SubwordRows.nativeRow ⟨14286849, by decide⟩ = Vector.replicate 9 0 :=
  SubwordBoundary.padding_row _ (by decide)

end Tests.GKRSubwordNative
