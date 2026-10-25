import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.WordMemoryUncached

namespace Airbender.Compiler.HistoryErasureNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/word-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryUncached.native inputs 52

end Airbender.Compiler.HistoryErasureNative.WordMemoryUncached
