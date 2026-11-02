import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeGUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks

namespace Airbender.Compiler.HelperValidityChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def original := NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.BlakeGUncached.native.slots
  Airbender.Compiler.HelperNative.BlakeGUncached.native.fields Airbender.Compiler.HelperNative.BlakeGUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank

end Airbender.Compiler.HelperValidityChecks.BlakeGUncached
