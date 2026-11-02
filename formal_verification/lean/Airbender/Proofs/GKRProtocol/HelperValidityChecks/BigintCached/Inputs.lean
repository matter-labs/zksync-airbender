import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.BigintCached
import Airbender.Proofs.GKRProtocol.HelperNative.BigintCached

namespace Airbender.Compiler.HelperValidityNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/bigint-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  source_model Airbender.Compiler.SourceContractNative.BigintCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BigintCached.native
  helper_model Airbender.Compiler.HelperNative.BigintCached.native
  memory_model Airbender.Compiler.MemoryNative.BigintCached.native inputs 276 phase 0

end Airbender.Compiler.HelperValidityNative.BigintCached
