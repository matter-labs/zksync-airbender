import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.WordMemoryUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.WordMemoryUncached

namespace Airbender.Compiler.HistoryErasureNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/word-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryUncached.native inputs 52
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.WordMemoryUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.WordMemoryUncached
