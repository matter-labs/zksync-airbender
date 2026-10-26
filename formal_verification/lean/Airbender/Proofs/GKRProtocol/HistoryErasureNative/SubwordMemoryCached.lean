import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.SubwordMemoryCached

namespace Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/subword-memory-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native inputs 68

end Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached
