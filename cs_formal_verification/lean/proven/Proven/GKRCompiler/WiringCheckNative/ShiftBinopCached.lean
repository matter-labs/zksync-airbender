module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.WiringCheckNative.ShiftBinopCachedBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringCheckNative.ShiftBinopCached
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.ShiftBinopCached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.ShiftBinopCached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.ShiftBinopCached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.ShiftBinopCached
