import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.SubwordMemoryCached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.SubwordMemoryCached

namespace Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/subword-memory-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native inputs 68
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.SubwordMemoryCached.originalChecked

end Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached
