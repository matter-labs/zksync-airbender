import Airbender.Proofs.GKRProtocol.CleanIdealNative.MulDivUncachedData

namespace Airbender.Compiler.CleanIdealNative.MulDivUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end Airbender.Compiler.CleanIdealNative.MulDivUncached
