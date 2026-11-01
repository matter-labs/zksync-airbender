import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.ShiftBinopUncached.Certificate
import Airbender.Proofs.GKRProtocol.SourceContractNative.ShiftBinopUncached

namespace Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/shift-binop-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native inputs 98
  phase 1 using_check Airbender.Compiler.HistoryErasureChecks.ShiftBinopUncached.originalChecked

end Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached
