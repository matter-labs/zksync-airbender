import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.ShiftBinopCached

namespace Airbender.Compiler.MemoryFrameNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/shift-binop-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopCached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopCached.native
  history_model Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native
  helper_model Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native
  counter_model Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native
  inputs 98 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.ShiftBinopCached
