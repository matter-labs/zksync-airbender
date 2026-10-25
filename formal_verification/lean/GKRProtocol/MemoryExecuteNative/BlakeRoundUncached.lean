import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.BlakeRoundUncached

namespace Airbender.Compiler.MemoryExecuteNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native
  helper_fields Airbender.Compiler.HelperNative.BlakeRoundUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native
  inputs 763

end Airbender.Compiler.MemoryExecuteNative.BlakeRoundUncached
