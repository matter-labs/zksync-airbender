import GKRProtocol.MemoryFrameImport
import GKRProtocol.CounterFrameNative.JumpBranchCached

namespace Airbender.Compiler.MemoryFrameNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_frame native from "artifacts/compiler/jump-branch-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchCached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchCached.native
  history_model Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native
  helper_model Airbender.Compiler.HelperValidityNative.JumpBranchCached.native
  counter_model Airbender.Compiler.CounterFrameNative.JumpBranchCached.native
  inputs 55 phase 3 start 0 stop 56

end Airbender.Compiler.MemoryFrameNative.JumpBranchCached
