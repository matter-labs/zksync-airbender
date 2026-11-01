import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeRoundCached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.BlakeRoundCached

namespace Airbender.Compiler.HistoryErasureNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/blake-round-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundCached.native inputs 763
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.BlakeRoundCached.originalChecked

end Airbender.Compiler.HistoryErasureNative.BlakeRoundCached
