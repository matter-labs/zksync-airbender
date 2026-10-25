import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.SubwordMemoryUncached

namespace Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/subword-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native
  inputs 68 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached
