import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BigintUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BigintUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BigintUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.BigintUncached.native.slots
  Airbender.Compiler.HelperNative.BigintUncached.native.fields Airbender.Compiler.HelperNative.BigintUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.MemoryNative.BigintUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.BigintUncached
