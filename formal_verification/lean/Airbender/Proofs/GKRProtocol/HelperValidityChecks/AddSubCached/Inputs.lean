import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.AddSubCached
import Airbender.Proofs.GKRProtocol.HelperNative.AddSubCached

namespace Airbender.Compiler.HelperValidityNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/add-sub-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubCached.native
  history_model Airbender.Compiler.HistoryErasureNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperNative.AddSubCached.native
  memory_model Airbender.Compiler.MemoryNative.AddSubCached.native inputs 48 phase 0

end Airbender.Compiler.HelperValidityNative.AddSubCached
