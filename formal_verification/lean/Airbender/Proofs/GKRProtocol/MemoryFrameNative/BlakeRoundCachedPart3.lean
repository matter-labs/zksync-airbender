import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeRoundCachedInputs

namespace Airbender.Compiler.MemoryFrameNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/blake-round-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native
  inputs 763 phase 1 start 192 stop 256

end Airbender.Compiler.MemoryFrameNative.BlakeRoundCached
