import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/mul-div-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivUncached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.MulDivUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.MulDivUncached.native
  inputs 71 phase 3 start 0 stop 56
  using_check Airbender.Compiler.MemoryFrameChecks.MulDivUncached.originalChecked

end Airbender.Compiler.MemoryFrameNative.MulDivUncached
