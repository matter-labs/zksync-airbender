import Airbender.Proofs.GKRProtocol.HelperValidityChecks.AddSubCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks

namespace Airbender.Compiler.HelperValidityChecks.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def original := NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.AddSubCached.native.profile
  Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement Airbender.Compiler.SourceContractNative.AddSubCached.native.slots
  Airbender.Compiler.HelperNative.AddSubCached.native.fields Airbender.Compiler.HelperNative.AddSubCached.native.placement
  Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.MemoryNative.AddSubCached.native.bank

end Airbender.Compiler.HelperValidityChecks.AddSubCached
