import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.MulDivUncached

namespace Airbender.Compiler.MemoryFrameNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/mul-div-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivUncached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.MulDivUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.MulDivUncached.native
  inputs 71 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.MulDivUncached
