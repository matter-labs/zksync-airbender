import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BigintCached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.BigintCached

namespace Airbender.Compiler.HistoryErasureNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/bigint-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  source_model Airbender.Compiler.SourceContractNative.BigintCached.native inputs 276
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.BigintCached.originalChecked

end Airbender.Compiler.HistoryErasureNative.BigintCached
