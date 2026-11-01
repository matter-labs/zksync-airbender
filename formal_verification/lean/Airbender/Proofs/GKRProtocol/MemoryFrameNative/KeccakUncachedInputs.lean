import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.KeccakUncached

namespace Airbender.Compiler.MemoryFrameNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/keccak-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakUncached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.KeccakUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.KeccakUncached.native
  inputs 266 phase 0 start 0 stop 210

end Airbender.Compiler.MemoryFrameNative.KeccakUncached
