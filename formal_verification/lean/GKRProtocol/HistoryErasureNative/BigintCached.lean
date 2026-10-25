import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.BigintCached

namespace Airbender.Compiler.HistoryErasureNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/bigint-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  source_model Airbender.Compiler.SourceContractNative.BigintCached.native inputs 277

end Airbender.Compiler.HistoryErasureNative.BigintCached
