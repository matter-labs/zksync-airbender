import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.HelperNative.SubwordMemoryUncached

namespace Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/subword-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native
  helper_model Airbender.Compiler.HelperNative.SubwordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native inputs 68 phase 0

end Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached
