import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.UnifiedUncached

namespace Airbender.Compiler.HistoryErasureNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/unified-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedUncached.native inputs 145

end Airbender.Compiler.HistoryErasureNative.UnifiedUncached
