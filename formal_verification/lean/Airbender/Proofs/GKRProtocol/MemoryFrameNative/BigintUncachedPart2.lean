import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BigintUncached
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BigintUncachedInputs

namespace Airbender.Compiler.MemoryFrameNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/bigint-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  memory_model Airbender.Compiler.MemoryNative.BigintUncached.native
  source_model Airbender.Compiler.SourceContractNative.BigintUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BigintUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BigintUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.BigintUncached.native
  inputs 276 phase 1 start 128 stop 192

end Airbender.Compiler.MemoryFrameNative.BigintUncached
