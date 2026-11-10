import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.HelperNative.WordMemoryCached

namespace Airbender.Compiler.HelperValidityNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/word-memory-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryCached.native
  history_model Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native
  helper_model Airbender.Compiler.HelperNative.WordMemoryCached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryCached.native inputs 52 phase 0

end Airbender.Compiler.HelperValidityNative.WordMemoryCached
