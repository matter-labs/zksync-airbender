module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.WiringCheckNative.AddSubCachedBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringCheckNative.AddSubCached
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.AddSubCached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.AddSubCached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.AddSubCached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.AddSubCached
