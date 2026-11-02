import Airbender.Proofs.GKRProtocol.HelperValidityChecks.KeccakUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.KeccakUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.KeccakUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.KeccakUncached.native.slots
  Airbender.Compiler.HelperNative.KeccakUncached.native.fields Airbender.Compiler.HelperNative.KeccakUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.KeccakUncached
