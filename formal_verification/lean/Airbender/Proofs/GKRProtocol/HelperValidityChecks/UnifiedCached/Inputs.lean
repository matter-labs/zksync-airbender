import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.HelperNative.UnifiedCached

namespace Airbender.Compiler.HelperValidityNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/unified-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedCached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperNative.UnifiedCached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedCached.native inputs 137 phase 0

end Airbender.Compiler.HelperValidityNative.UnifiedCached
