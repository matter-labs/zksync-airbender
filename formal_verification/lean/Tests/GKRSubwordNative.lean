import Airbender.Proofs.GKRProtocol.MaterializedNative.SubwordMemoryCached

namespace Tests.GKRSubwordNative
open Airbender Airbender.Compiler
set_option warningAsError true

private abbrev nativeSetup := Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model

theorem half_rom_tag :
    nativeSetup.value ⟨655361, by decide⟩ (.generic 8) = 44 := by
  rw [nativeSetup.generic_cell_value _ (⟨8, by decide⟩ : Fin 9)]
  decide +kernel

theorem byte_rom_tag :
    nativeSetup.value ⟨4849665, by decide⟩ (.generic 8) = 45 := by
  rw [nativeSetup.generic_cell_value _ (⟨8, by decide⟩ : Fin 9)]
  decide +kernel

theorem decoder_keeps_distinct_tag :
    nativeSetup.value ⟨13238273, by decide⟩ (.generic 8) = 46 := by
  rw [nativeSetup.generic_cell_value _ (⟨8, by decide⟩ : Fin 9)]
  decide +kernel

/-- Every generic coordinate of this committed padding row is zero. -/
theorem committed_padding_is_disabled (column : Fin 9) :
    nativeSetup.value ⟨14286849, by decide⟩ (.generic column) = 0 := by
  rw [nativeSetup.generic_cell_value _ column]
  fin_cases column <;> decide +kernel

end Tests.GKRSubwordNative
