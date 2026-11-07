import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeGCached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGCached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/blake-g-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeGCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeGCached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeGCached.native
  inputs 112 phase 3 start 0 stop 140
  using_check Airbender.Compiler.MemoryFrameChecks.BlakeGCached.originalChecked

end Airbender.Compiler.MemoryFrameNative.BlakeGCached
