import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.ShiftBinopUncached

namespace Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/shift-binop-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopUncached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native
  inputs 98 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached
