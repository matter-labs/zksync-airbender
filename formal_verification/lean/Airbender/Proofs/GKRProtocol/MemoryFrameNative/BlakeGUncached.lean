import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeGUncached

namespace Airbender.Compiler.MemoryFrameNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/blake-g-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeGUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeGUncached.native
  inputs 113 phase 3 start 0 stop 140

end Airbender.Compiler.MemoryFrameNative.BlakeGUncached
