import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BigintCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BigintCached.native.profile
  Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement Airbender.Compiler.SourceContractNative.BigintCached.native.slots
  Airbender.Compiler.HelperNative.BigintCached.native.fields Airbender.Compiler.HelperNative.BigintCached.native.placement
  Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.MemoryNative.BigintCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.BigintCached
