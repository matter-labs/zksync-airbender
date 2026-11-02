import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.HelperNative.BlakeGUncached

namespace Airbender.Compiler.HelperValidityNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/blake-g-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native
  helper_model Airbender.Compiler.HelperNative.BlakeGUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGUncached.native inputs 112 phase 0

end Airbender.Compiler.HelperValidityNative.BlakeGUncached
