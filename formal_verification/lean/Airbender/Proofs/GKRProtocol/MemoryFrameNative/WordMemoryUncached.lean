import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryUncached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/word-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native
  inputs 52 phase 3 start 0 stop 56
  using_check Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached.originalChecked

end Airbender.Compiler.MemoryFrameNative.WordMemoryUncached
