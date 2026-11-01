import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.KeccakUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.KeccakUncached

namespace Airbender.Compiler.HistoryErasureNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/keccak-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakUncached.native inputs 266
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.KeccakUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.KeccakUncached
