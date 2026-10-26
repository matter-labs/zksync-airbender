import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.AddSubUncached

namespace Airbender.Compiler.HistoryErasureNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/add-sub-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubUncached.native inputs 48

end Airbender.Compiler.HistoryErasureNative.AddSubUncached
