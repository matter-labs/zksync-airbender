import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.BlakeRoundUncached

namespace Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_history_erasure native from "artifacts/compiler/blake-round-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native inputs 763

end Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached
