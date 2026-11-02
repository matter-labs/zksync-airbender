import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.BigintUncached
import Airbender.Proofs.GKRProtocol.HelperNative.BigintUncached

namespace Airbender.Compiler.HelperValidityNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/bigint-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  source_model Airbender.Compiler.SourceContractNative.BigintUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BigintUncached.native
  helper_model Airbender.Compiler.HelperNative.BigintUncached.native
  memory_model Airbender.Compiler.MemoryNative.BigintUncached.native inputs 276 phase 0

end Airbender.Compiler.HelperValidityNative.BigintUncached
