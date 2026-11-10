import Airbender.Proofs.GKRProtocol.CleanIdealNative.BlakeGCachedData

namespace Airbender.Compiler.CleanIdealNative.BlakeGCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end Airbender.Compiler.CleanIdealNative.BlakeGCached
