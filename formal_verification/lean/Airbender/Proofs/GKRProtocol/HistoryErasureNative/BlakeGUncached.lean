import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeGUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.BlakeGUncached

namespace Airbender.Compiler.HistoryErasureNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/blake-g-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGUncached.native inputs 112
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.BlakeGUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.BlakeGUncached
