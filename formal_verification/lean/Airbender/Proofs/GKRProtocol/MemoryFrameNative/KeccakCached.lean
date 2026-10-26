import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.KeccakCached

namespace Airbender.Compiler.MemoryFrameNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/keccak-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakCached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakCached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakCached.native
  helper_model Airbender.Compiler.HelperValidityNative.KeccakCached.native
  counter_model Airbender.Compiler.CounterFrameNative.KeccakCached.native
  inputs 267 phase 3 start 0 stop 210

end Airbender.Compiler.MemoryFrameNative.KeccakCached
