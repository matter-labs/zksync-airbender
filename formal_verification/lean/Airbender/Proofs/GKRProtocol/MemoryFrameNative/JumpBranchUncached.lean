import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/jump-branch-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchUncached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native
  inputs 55 phase 3 start 0 stop 56
  using_check Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached.originalChecked

end Airbender.Compiler.MemoryFrameNative.JumpBranchUncached
