import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.MulDivCached

namespace Airbender.Compiler.HistoryErasureNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/mul-div-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivCached.native inputs 71

end Airbender.Compiler.HistoryErasureNative.MulDivCached
