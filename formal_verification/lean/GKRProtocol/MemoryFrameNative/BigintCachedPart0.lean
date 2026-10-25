import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.BigintCached
import GKRProtocol.MemoryFrameNative.BigintCachedInputs

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
  inputs 277 phase 1 start 0 stop 64

end Airbender.Compiler.MemoryFrameNative.BigintCached
