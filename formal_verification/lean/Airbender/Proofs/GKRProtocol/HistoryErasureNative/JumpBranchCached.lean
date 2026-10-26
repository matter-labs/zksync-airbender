import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.JumpBranchCached

namespace Airbender.Compiler.HistoryErasureNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/jump-branch-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchCached.native inputs 55

end Airbender.Compiler.HistoryErasureNative.JumpBranchCached
