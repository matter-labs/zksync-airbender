import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.HelperNative.KeccakUncached

namespace Airbender.Compiler.HelperValidityNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/keccak-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperNative.KeccakUncached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakUncached.native inputs 266 phase 0

end Airbender.Compiler.HelperValidityNative.KeccakUncached
