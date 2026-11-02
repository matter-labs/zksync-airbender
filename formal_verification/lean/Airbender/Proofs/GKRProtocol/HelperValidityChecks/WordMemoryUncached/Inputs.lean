import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.HelperNative.WordMemoryUncached

namespace Airbender.Compiler.HelperValidityNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/word-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native
  helper_model Airbender.Compiler.HelperNative.WordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryUncached.native inputs 52 phase 0

end Airbender.Compiler.HelperValidityNative.WordMemoryUncached
