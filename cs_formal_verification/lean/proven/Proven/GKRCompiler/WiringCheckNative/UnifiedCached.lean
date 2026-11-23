module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.WiringCheckNative.UnifiedCachedBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringCheckNative.UnifiedCached
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.UnifiedCached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.UnifiedCached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.UnifiedCached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.UnifiedCached
