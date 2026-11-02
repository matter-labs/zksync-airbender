import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.HelperNative.UnifiedUncached

namespace Airbender.Compiler.HelperValidityNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/unified-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native
  helper_model Airbender.Compiler.HelperNative.UnifiedUncached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedUncached.native inputs 137 phase 0

end Airbender.Compiler.HelperValidityNative.UnifiedUncached
