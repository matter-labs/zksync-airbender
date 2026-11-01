import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryCached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/word-memory-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryCached.native
  history_model Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native
  helper_model Airbender.Compiler.HelperValidityNative.WordMemoryCached.native
  counter_model Airbender.Compiler.CounterFrameNative.WordMemoryCached.native
  inputs 52 phase 3 start 0 stop 56
  using_check Airbender.Compiler.MemoryFrameChecks.WordMemoryCached.originalChecked

end Airbender.Compiler.MemoryFrameNative.WordMemoryCached
