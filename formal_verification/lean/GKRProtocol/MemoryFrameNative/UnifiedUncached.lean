import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.UnifiedUncached

namespace Airbender.Compiler.MemoryFrameNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/unified-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedUncached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.UnifiedUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.UnifiedUncached.native
  inputs 145 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.UnifiedUncached
