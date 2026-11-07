import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.HelperNative.SubwordMemoryCached

namespace Airbender.Compiler.HelperValidityNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_helper_validity native from "artifacts/compiler/subword-memory-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native
  history_model Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native
  helper_model Airbender.Compiler.HelperNative.SubwordMemoryCached.native
  memory_model Airbender.Compiler.MemoryNative.SubwordMemoryCached.native inputs 68 phase 0

end Airbender.Compiler.HelperValidityNative.SubwordMemoryCached
