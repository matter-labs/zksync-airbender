import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubCached

namespace Airbender.Compiler.MemoryFrameNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/add-sub-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  memory_model Airbender.Compiler.MemoryNative.AddSubCached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubCached.native
  history_model Airbender.Compiler.HistoryErasureNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperValidityNative.AddSubCached.native
  counter_model Airbender.Compiler.CounterFrameNative.AddSubCached.native
  inputs 48 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.AddSubCached
