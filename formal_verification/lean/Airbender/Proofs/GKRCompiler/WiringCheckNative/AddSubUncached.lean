import Airbender.Proofs.GKRCompiler.WiringCheckNative.AddSubUncachedBindings

namespace Airbender.Compiler.WiringCheckNative.AddSubUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.AddSubUncached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.AddSubUncached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.AddSubUncached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.AddSubUncached
