import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.JumpBranchCached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.JumpBranchCached

namespace Airbender.Compiler.HistoryErasureNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/jump-branch-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchCached.native inputs 55
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.JumpBranchCached.originalChecked

end Airbender.Compiler.HistoryErasureNative.JumpBranchCached
