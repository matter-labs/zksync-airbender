import Airbender.Proofs.GKRProtocol.HelperValidityChecks.KeccakUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks

namespace Airbender.Compiler.HelperValidityChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def original := NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.KeccakUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.KeccakUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.KeccakUncached.native.slots
  Airbender.Compiler.HelperNative.KeccakUncached.native.fields Airbender.Compiler.HelperNative.KeccakUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.MemoryNative.KeccakUncached.native.bank

end Airbender.Compiler.HelperValidityChecks.KeccakUncached
