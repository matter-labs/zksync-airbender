import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchCached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/jump-branch-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchCached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchCached.native
  history_model Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native
  helper_model Airbender.Compiler.HelperValidityNative.JumpBranchCached.native
  counter_model Airbender.Compiler.CounterFrameNative.JumpBranchCached.native
  inputs 55 phase 3 start 0 stop 56
  using_check Airbender.Compiler.MemoryFrameChecks.JumpBranchCached.originalChecked

end Airbender.Compiler.MemoryFrameNative.JumpBranchCached
