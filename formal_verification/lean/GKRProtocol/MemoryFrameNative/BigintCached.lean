import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.BigintCached
import GKRProtocol.MemoryFrameNative.BigintCachedInputs
import GKRProtocol.MemoryFrameNative.BigintCachedPart0
import GKRProtocol.MemoryFrameNative.BigintCachedPart1
import GKRProtocol.MemoryFrameNative.BigintCachedPart2
import GKRProtocol.MemoryFrameNative.BigintCachedPart3
import GKRProtocol.MemoryFrameNative.BigintCachedPart4

namespace Airbender.Compiler.MemoryFrameNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/bigint-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  memory_model Airbender.Compiler.MemoryNative.BigintCached.native
  source_model Airbender.Compiler.SourceContractNative.BigintCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BigintCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BigintCached.native
  counter_model Airbender.Compiler.CounterFrameNative.BigintCached.native
  inputs 277 phase 2 start 0 stop 280

end Airbender.Compiler.MemoryFrameNative.BigintCached
