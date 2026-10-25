import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.UnifiedCached

namespace Airbender.Compiler.HistoryErasureNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/unified-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedCached.native inputs 145

end Airbender.Compiler.HistoryErasureNative.UnifiedCached
