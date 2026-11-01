import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.UnifiedUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.UnifiedUncached

namespace Airbender.Compiler.HistoryErasureNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/unified-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedUncached.native inputs 137
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.UnifiedUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.UnifiedUncached
