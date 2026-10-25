import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.MulDivUncached

namespace Airbender.Compiler.HistoryErasureNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/mul-div-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivUncached.native inputs 71

end Airbender.Compiler.HistoryErasureNative.MulDivUncached
