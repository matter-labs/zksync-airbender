import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.SubwordMemoryCached

namespace Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/subword-memory-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  memory_model Airbender.Compiler.MemoryNative.SubwordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native
  history_model Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native
  helper_model Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native
  counter_model Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native
  inputs 68 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached
