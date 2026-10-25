import GKRProtocol.ROMNative.WordMemoryPublic

namespace Tests.GKRNativeROM
open Airbender Airbender.Compiler
open Airbender.Compiler.ROMNative.WordMemory
set_option warningAsError true

theorem decoder_region_excluded :
    nativeSetup.value ⟨1048577, by decide⟩ (.generic 8) ≠ 34 := by decide +kernel

theorem committed_padding_excluded :
    nativeSetup.value ⟨2097153, by decide⟩ (.generic 8) ≠ 34 := by decide +kernel

theorem final_rom_word_address :
    nativeSetup.value ⟨1048576, by decide⟩ (.generic 0) = 4194300 := by decide +kernel

theorem image_padding_is_zero :
    nativeSetup.value ⟨5, by decide⟩ (.generic 1) = 0 ∧
    nativeSetup.value ⟨5, by decide⟩ (.generic 2) = 0 := by decide +kernel

end Tests.GKRNativeROM
