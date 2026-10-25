import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.WordMemoryUncached

namespace Airbender.Compiler.MemoryFrameNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/word-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native
  inputs 52 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.WordMemoryUncached
