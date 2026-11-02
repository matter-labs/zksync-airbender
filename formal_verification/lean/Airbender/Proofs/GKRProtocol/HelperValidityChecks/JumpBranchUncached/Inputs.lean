import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.HelperNative.JumpBranchUncached

namespace Airbender.Compiler.HelperValidityNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/jump-branch-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native
  helper_model Airbender.Compiler.HelperNative.JumpBranchUncached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchUncached.native inputs 55 phase 0

end Airbender.Compiler.HelperValidityNative.JumpBranchUncached
