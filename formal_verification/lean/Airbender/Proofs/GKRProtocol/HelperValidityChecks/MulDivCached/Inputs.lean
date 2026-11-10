import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.MulDivCached
import Airbender.Proofs.GKRProtocol.HelperNative.MulDivCached

namespace Airbender.Compiler.HelperValidityNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/mul-div-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivCached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivCached.native
  helper_model Airbender.Compiler.HelperNative.MulDivCached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivCached.native inputs 71 phase 0

end Airbender.Compiler.HelperValidityNative.MulDivCached
