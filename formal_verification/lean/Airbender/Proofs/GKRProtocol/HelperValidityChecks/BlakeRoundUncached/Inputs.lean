import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.HelperNative.BlakeRoundUncached

namespace Airbender.Compiler.HelperValidityNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/blake-round-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native
  helper_model Airbender.Compiler.HelperNative.BlakeRoundUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundUncached.native inputs 763 phase 0

end Airbender.Compiler.HelperValidityNative.BlakeRoundUncached
