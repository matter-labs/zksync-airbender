import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeGCached

namespace Airbender.Compiler.MemoryFrameNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/blake-g-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeGCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeGCached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeGCached.native
  inputs 113 phase 3 start 0 stop 140

end Airbender.Compiler.MemoryFrameNative.BlakeGCached
