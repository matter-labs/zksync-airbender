import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.BlakeGCached
import Airbender.Proofs.GKRProtocol.HelperNative.BlakeGCached

namespace Airbender.Compiler.HelperValidityNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/blake-g-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeGCached.native
  helper_model Airbender.Compiler.HelperNative.BlakeGCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGCached.native inputs 112 phase 0

end Airbender.Compiler.HelperValidityNative.BlakeGCached
