import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.BigintUncached

namespace Airbender.Compiler.HistoryErasureNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/bigint-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  source_model Airbender.Compiler.SourceContractNative.BigintUncached.native inputs 277

end Airbender.Compiler.HistoryErasureNative.BigintUncached
