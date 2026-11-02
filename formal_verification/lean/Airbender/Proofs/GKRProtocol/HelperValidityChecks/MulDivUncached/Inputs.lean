import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.HelperNative.MulDivUncached

namespace Airbender.Compiler.HelperValidityNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/mul-div-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperNative.MulDivUncached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivUncached.native inputs 71 phase 0

end Airbender.Compiler.HelperValidityNative.MulDivUncached
