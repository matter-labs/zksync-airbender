import Airbender.Proofs.GKRProtocol.ROMNative.UnifiedPublic

namespace Tests.GKRUnifiedROM
open Airbender Airbender.Compiler
open Airbender.Compiler.ROMNative.UnifiedTag
set_option warningAsError true

theorem previous_fixed_row_excluded :
    nativeSetup.value ⟨590080, by decide⟩ (.generic 9) ≠ 34 := by
  rw [tag_value]
  decide +kernel

theorem next_fixed_row_excluded :
    nativeSetup.value ⟨1638657, by decide⟩ (.generic 9) ≠ 34 := by
  rw [tag_value]
  decide +kernel

theorem decoder_row_excluded :
    nativeSetup.value ⟨2097537, by decide⟩ (.generic 9) ≠ 34 := by
  rw [tag_value]
  decide +kernel

theorem both_rom_endpoints_selected :
    nativeSetup.value ⟨590081, by decide⟩ (.generic 9) = 34 ∧
    nativeSetup.value ⟨1638656, by decide⟩ (.generic 9) = 34 := by
  constructor <;> rw [tag_value] <;> decide +kernel

end Tests.GKRUnifiedROM
