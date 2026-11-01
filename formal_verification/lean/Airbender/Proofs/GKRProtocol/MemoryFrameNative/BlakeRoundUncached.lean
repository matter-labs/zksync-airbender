import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeRoundUncached.Certificate

namespace Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_memory_frame native from "artifacts/compiler/blake-round-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native
  inputs 763 phase 3 start 0 stop 616
  using_check Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached.originalChecked

end Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached
