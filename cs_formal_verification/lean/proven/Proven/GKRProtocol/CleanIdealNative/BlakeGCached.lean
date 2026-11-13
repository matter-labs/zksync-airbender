module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.BlakeGCachedData

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.BlakeGCached
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end Airbender.Compiler.CleanIdealNative.BlakeGCached
