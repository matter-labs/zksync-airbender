import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.UnifiedCached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/unified-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedCached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedCached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperValidityNative.UnifiedCached.native
  counter_model Airbender.Compiler.CounterFrameNative.UnifiedCached.native
  inputs 137 phase 3 start 0 stop 56
  using_check Airbender.Compiler.MemoryFrameChecks.UnifiedCached.originalChecked

end Airbender.Compiler.MemoryFrameNative.UnifiedCached
