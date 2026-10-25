import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.BlakeGCached

namespace Airbender.Compiler.HistoryErasureNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/blake-g-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGCached.native inputs 113

end Airbender.Compiler.HistoryErasureNative.BlakeGCached
