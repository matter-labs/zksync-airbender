import Airbender.Proofs.GKRProtocol.HelperValidityChecks.KeccakCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks

namespace Airbender.Compiler.HelperValidityChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def original := NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.KeccakCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.KeccakCached.native.profile
  Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement Airbender.Compiler.SourceContractNative.KeccakCached.native.slots
  Airbender.Compiler.HelperNative.KeccakCached.native.fields Airbender.Compiler.HelperNative.KeccakCached.native.placement
  Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.MemoryNative.KeccakCached.native.bank

end Airbender.Compiler.HelperValidityChecks.KeccakCached
