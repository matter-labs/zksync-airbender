import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.AddSubUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.AddSubUncached

namespace Airbender.Compiler.HistoryErasureNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/add-sub-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubUncached.native inputs 48
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.AddSubUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.AddSubUncached
