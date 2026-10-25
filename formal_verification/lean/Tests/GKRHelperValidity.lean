import GKRProtocol.HelperValidityNative.AddSubUncached

namespace Tests.GKRHelperValidity
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem rejects_erasing_current_clock :
    erasureCheck [FullArithmeticNative.AddSubUncached.native.helperPlacement.memory.original 21]
      SourceContractNative.AddSubUncached.native.protectedPolynomials = false := by decide +kernel

theorem rejects_borrow_aliasing_current_clock :
    HelperNative.AddSubUncached.native.fields.all (Source.HelperField.borrowCheck
      FullArithmeticNative.AddSubUncached.native.helperPlacement
      (fun _ : Fin 3 => FullArithmeticNative.AddSubUncached.native.helperPlacement.memory.original 21)) = false := by
  decide +kernel

private def zeroMemory : Source.MemoryValues :=
  ⟨fun _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- Positivity on padding clocks is necessary: zero history at clock zero
fails the unconditional high-difference range query. -/
theorem zero_clock_rejects_zero_history :
    (((Source.comparisonFields Source.MemoryWord.zero Source.MemoryWord.zero 0).2).value
      (Source.canonicalHelpers zeroMemory [(Source.MemoryWord.zero, Source.MemoryWord.zero)])).val = 524288 := by
  decide +kernel

/-- History normalization preserves every masked effect at every challenge. -/
theorem inactive_effect_unchanged (coordinates : List (Fin n))
    (values : Fin n → Source.BaseField) (effect : (Fin n → Source.BaseField) → Source.BaseField) :
    maskProduct 0 (effect (inactiveHistory coordinates 0 values)) = maskProduct 0 (effect values) :=
  inactiveHistory_maskProduct (RingHom.id Source.BaseField) coordinates 0 values effect

end Tests.GKRHelperValidity
