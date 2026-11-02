import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.HelperNative.ShiftBinopUncached

namespace Airbender.Compiler.HelperValidityNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/shift-binop-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native
  helper_model Airbender.Compiler.HelperNative.ShiftBinopUncached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopUncached.native inputs 98 phase 0

end Airbender.Compiler.HelperValidityNative.ShiftBinopUncached
