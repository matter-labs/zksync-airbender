import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.WordMemoryCached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.WordMemoryCached

namespace Airbender.Compiler.HistoryErasureNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/word-memory-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryCached.native inputs 52
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.WordMemoryCached.originalChecked

end Airbender.Compiler.HistoryErasureNative.WordMemoryCached
