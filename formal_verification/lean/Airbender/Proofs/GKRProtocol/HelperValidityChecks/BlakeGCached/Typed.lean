import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeGCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks

namespace Airbender.Compiler.HelperValidityChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def original := NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BlakeGCached.native.profile
  Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement Airbender.Compiler.SourceContractNative.BlakeGCached.native.slots
  Airbender.Compiler.HelperNative.BlakeGCached.native.fields Airbender.Compiler.HelperNative.BlakeGCached.native.placement
  Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.MemoryNative.BlakeGCached.native.bank

end Airbender.Compiler.HelperValidityChecks.BlakeGCached
