import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.BlakeGUncached

namespace Airbender.Compiler.HistoryErasureNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/blake-g-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGUncached.native inputs 113

end Airbender.Compiler.HistoryErasureNative.BlakeGUncached
