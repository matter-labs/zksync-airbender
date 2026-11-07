import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.HelperNative.BlakeRoundCached

namespace Airbender.Compiler.HelperValidityNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/blake-round-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native
  helper_model Airbender.Compiler.HelperNative.BlakeRoundCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundCached.native inputs 763 phase 0

end Airbender.Compiler.HelperValidityNative.BlakeRoundCached
