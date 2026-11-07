import Airbender.Proofs.GKRCompiler.WiringCheckNative.BlakeRoundCachedBindings

namespace Airbender.Compiler.WiringCheckNative.BlakeRoundCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.BlakeRoundCached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.BlakeRoundCached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.BlakeRoundCached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.BlakeRoundCached
