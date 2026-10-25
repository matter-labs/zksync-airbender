import GKRProtocol.ShiftSetupNative

namespace Tests.GKRShiftSetup
open Airbender Airbender.Compiler
set_option warningAsError true

theorem decoder_cannot_supply_zero_padding
    (row : Fin ShiftSetupNative.nativeSetup.imported.data.length)
    (lower : 524545 ≤ row.val) (upper : row.val < 1573121) :
    ShiftSetupNative.nativeSetup.value row (.generic 8) ≠ 0 := by
  intro selected
  rcases ShiftSetupNative.padding_domain row selected with before | after
  · omega
  · omega

theorem zero_row_is_retained :
    (Verification.shiftBinopTable (p := babyBearModulus)).Contains #[]
      (Vector.replicate 10 0) := by
  exact ⟨0, by decide +kernel⟩

theorem native_padding_refines_dummy
    (row : Fin ShiftSetupNative.nativeSetup.imported.data.length) (lower : 1573121 ≤ row.val) :
    (ShiftSetupNative.nativeSetup.imported.data.row row).map
      (fun entry : Int => (entry : Source.BaseField)) = Vector.replicate 10 0 := by
  rw [ShiftSetupNative.padding_row row lower]
  decide +kernel

end Tests.GKRShiftSetup
