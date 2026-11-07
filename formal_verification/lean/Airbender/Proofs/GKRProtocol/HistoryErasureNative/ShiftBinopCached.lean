import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.ShiftBinopCached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.ShiftBinopCached

namespace Airbender.Compiler.HistoryErasureNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/shift-binop-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopCached.native inputs 98
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.ShiftBinopCached.originalChecked

end Airbender.Compiler.HistoryErasureNative.ShiftBinopCached
