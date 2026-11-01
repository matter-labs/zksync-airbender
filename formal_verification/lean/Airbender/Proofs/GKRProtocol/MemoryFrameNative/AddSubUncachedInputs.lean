import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubUncached

namespace Airbender.Compiler.MemoryFrameNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/add-sub-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  memory_model Airbender.Compiler.MemoryNative.AddSubUncached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.AddSubUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.AddSubUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.AddSubUncached.native
  inputs 48 phase 0 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.AddSubUncached
