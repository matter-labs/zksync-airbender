import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.KeccakUncached

namespace Airbender.Compiler.HistoryErasureNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/keccak-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakUncached.native inputs 267

end Airbender.Compiler.HistoryErasureNative.KeccakUncached
