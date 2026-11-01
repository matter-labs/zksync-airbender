import Airbender.Proofs.GKRProtocol.CleanIdealNative.BlakeGUncachedData

namespace Airbender.Compiler.CleanIdealNative.BlakeGUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end Airbender.Compiler.CleanIdealNative.BlakeGUncached
