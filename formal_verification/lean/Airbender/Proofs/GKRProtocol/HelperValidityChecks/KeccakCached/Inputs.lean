import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.KeccakCached
import Airbender.Proofs.GKRProtocol.HelperNative.KeccakCached

namespace Airbender.Compiler.HelperValidityNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/keccak-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakCached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakCached.native
  helper_model Airbender.Compiler.HelperNative.KeccakCached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakCached.native inputs 266 phase 0

end Airbender.Compiler.HelperValidityNative.KeccakCached
