import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.HelperNative.JumpBranchCached

namespace Airbender.Compiler.HelperValidityNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/jump-branch-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchCached.native
  history_model Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native
  helper_model Airbender.Compiler.HelperNative.JumpBranchCached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchCached.native inputs 55 phase 0

end Airbender.Compiler.HelperValidityNative.JumpBranchCached
