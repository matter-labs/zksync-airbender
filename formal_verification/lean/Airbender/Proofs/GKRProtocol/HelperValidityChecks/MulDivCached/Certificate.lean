import Airbender.Proofs.GKRProtocol.HelperValidityChecks.MulDivCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.MulDivCached.native.profile
  Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement Airbender.Compiler.SourceContractNative.MulDivCached.native.slots
  Airbender.Compiler.HelperNative.MulDivCached.native.fields Airbender.Compiler.HelperNative.MulDivCached.native.placement
  Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.MulDivCached
