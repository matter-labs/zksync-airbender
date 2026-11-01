import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.UnifiedCached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.UnifiedCached

namespace Airbender.Compiler.HistoryErasureNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/unified-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedCached.native inputs 137
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.UnifiedCached.originalChecked

end Airbender.Compiler.HistoryErasureNative.UnifiedCached
