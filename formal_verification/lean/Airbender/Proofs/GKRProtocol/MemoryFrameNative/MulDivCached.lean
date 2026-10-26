import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.MulDivCached

namespace Airbender.Compiler.MemoryFrameNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/mul-div-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivCached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivCached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivCached.native
  helper_model Airbender.Compiler.HelperValidityNative.MulDivCached.native
  counter_model Airbender.Compiler.CounterFrameNative.MulDivCached.native
  inputs 71 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.MulDivCached
