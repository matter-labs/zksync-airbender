import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.AddSubCached

namespace Airbender.Compiler.HistoryErasureNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/add-sub-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubCached.native inputs 48 phase 0

end Airbender.Compiler.HistoryErasureNative.AddSubCached
