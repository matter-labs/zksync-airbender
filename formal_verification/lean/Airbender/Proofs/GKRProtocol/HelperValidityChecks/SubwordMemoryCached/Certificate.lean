import Airbender.Proofs.GKRProtocol.HelperValidityChecks.SubwordMemoryCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.profile
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.slots
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.SubwordMemoryCached
