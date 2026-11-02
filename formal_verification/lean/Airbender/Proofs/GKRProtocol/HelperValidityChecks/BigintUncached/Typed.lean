import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BigintUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks

namespace Airbender.Compiler.HelperValidityChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def original := NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BigintUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BigintUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.BigintUncached.native.slots
  Airbender.Compiler.HelperNative.BigintUncached.native.fields Airbender.Compiler.HelperNative.BigintUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.MemoryNative.BigintUncached.native.bank

end Airbender.Compiler.HelperValidityChecks.BigintUncached
