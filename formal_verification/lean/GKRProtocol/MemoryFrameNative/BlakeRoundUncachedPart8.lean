import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.BlakeRoundUncached
import GKRProtocol.MemoryFrameNative.BlakeRoundUncachedInputs

namespace Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/blake-round-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native
  inputs 763 phase 1 start 512 stop 576

end Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached
