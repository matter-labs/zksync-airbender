module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.AddSubCachedData

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.AddSubCached
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end Airbender.Compiler.CleanIdealNative.AddSubCached
