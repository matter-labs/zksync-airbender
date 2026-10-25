import GKRProtocol.HistoryErasureImport
import GKRProtocol.SourceContractNative.KeccakCached

namespace Airbender.Compiler.HistoryErasureNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/keccak-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakCached.native inputs 267

end Airbender.Compiler.HistoryErasureNative.KeccakCached
