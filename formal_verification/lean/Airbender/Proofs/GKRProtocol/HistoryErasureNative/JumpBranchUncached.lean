import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.JumpBranchUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.JumpBranchUncached

namespace Airbender.Compiler.HistoryErasureNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/jump-branch-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchUncached.native inputs 55
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.JumpBranchUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.JumpBranchUncached
