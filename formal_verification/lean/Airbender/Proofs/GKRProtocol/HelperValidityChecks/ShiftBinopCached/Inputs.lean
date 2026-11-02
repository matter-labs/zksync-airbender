import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.HelperNative.ShiftBinopCached

namespace Airbender.Compiler.HelperValidityNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/shift-binop-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopCached.native
  history_model Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native
  helper_model Airbender.Compiler.HelperNative.ShiftBinopCached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopCached.native inputs 98 phase 0

end Airbender.Compiler.HelperValidityNative.ShiftBinopCached
