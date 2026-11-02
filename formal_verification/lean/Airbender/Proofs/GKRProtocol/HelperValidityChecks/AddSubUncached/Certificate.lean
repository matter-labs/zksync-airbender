import Airbender.Proofs.GKRProtocol.HelperValidityChecks.AddSubUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.AddSubUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.AddSubUncached.native.slots
  Airbender.Compiler.HelperNative.AddSubUncached.native.fields Airbender.Compiler.HelperNative.AddSubUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.AddSubUncached
