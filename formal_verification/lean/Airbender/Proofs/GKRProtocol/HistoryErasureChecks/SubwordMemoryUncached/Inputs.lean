import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.SubwordMemoryUncached

namespace Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_history_erasure native from "artifacts/compiler/subword-memory-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native inputs 68 phase 0

end Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached
