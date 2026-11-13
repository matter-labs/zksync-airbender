module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.UnifiedCachedBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.UnifiedCached
set_option maxRecDepth 32768

theorem rowsChecked : CleanIdealRows.check babyBearModulus rowCapture = true := by decide +kernel
theorem checked : CleanIdealChecks.check babyBearModulus capture = true :=
  CleanIdealRows.check_sound babyBearModulus rowCapture sources rowsChecked
end Airbender.Compiler.CleanIdealNative.UnifiedCached
