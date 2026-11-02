import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.HelperNative.AddSubUncached

namespace Airbender.Compiler.HelperValidityNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/add-sub-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.AddSubUncached.native
  helper_model Airbender.Compiler.HelperNative.AddSubUncached.native
  memory_model Airbender.Compiler.MemoryNative.AddSubUncached.native inputs 48 phase 0

end Airbender.Compiler.HelperValidityNative.AddSubUncached
