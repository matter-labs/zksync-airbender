import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.UnifiedCached

namespace Airbender.Compiler.MemoryFrameNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/unified-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedCached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedCached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperValidityNative.UnifiedCached.native
  counter_model Airbender.Compiler.CounterFrameNative.UnifiedCached.native
  inputs 145 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.UnifiedCached
