import Airbender.Proofs.GKRProtocol.FullArithmeticNative.UnifiedUncachedNumericBindings

namespace Airbender.Compiler.FullArithmeticNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem numericChecked : NumericArithmeticChecks.check babyBearModulus numericCapture = true := by decide +kernel

theorem numericFullChecked : FullArithmeticChecks.check native.addresses native.artifact native.certificate = true :=
  NumericArithmeticChecks.full_check _ _ _ _ numericBindings numericChecked

end Airbender.Compiler.FullArithmeticNative.UnifiedUncached
