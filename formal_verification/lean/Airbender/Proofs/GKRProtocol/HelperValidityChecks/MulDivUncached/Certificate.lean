import Airbender.Proofs.GKRProtocol.HelperValidityChecks.MulDivUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.MulDivUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.MulDivUncached.native.slots
  Airbender.Compiler.HelperNative.MulDivUncached.native.fields Airbender.Compiler.HelperNative.MulDivUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.MulDivUncached
