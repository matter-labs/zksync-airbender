import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.ShiftBinopUncached

namespace Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/shift-binop-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native inputs 98

end Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached
