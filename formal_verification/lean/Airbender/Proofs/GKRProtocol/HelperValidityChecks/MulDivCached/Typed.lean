import Airbender.Proofs.GKRProtocol.HelperValidityChecks.MulDivCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks

namespace Airbender.Compiler.HelperValidityChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def original := NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.MulDivCached.native.profile
  Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement Airbender.Compiler.SourceContractNative.MulDivCached.native.slots
  Airbender.Compiler.HelperNative.MulDivCached.native.fields Airbender.Compiler.HelperNative.MulDivCached.native.placement
  Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.MemoryNative.MulDivCached.native.bank

end Airbender.Compiler.HelperValidityChecks.MulDivCached
