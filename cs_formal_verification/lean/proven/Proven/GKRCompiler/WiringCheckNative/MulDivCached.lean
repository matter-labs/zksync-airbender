module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.WiringCheckNative.MulDivCachedBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringCheckNative.MulDivCached
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.MulDivCached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.MulDivCached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.MulDivCached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.MulDivCached
