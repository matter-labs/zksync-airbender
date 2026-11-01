import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BigintUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.BigintUncached

namespace Airbender.Compiler.HistoryErasureNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/bigint-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  source_model Airbender.Compiler.SourceContractNative.BigintUncached.native inputs 276
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.BigintUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.BigintUncached
