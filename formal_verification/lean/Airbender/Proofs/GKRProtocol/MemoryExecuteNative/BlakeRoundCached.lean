import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeRoundCached

namespace Airbender.Compiler.MemoryExecuteNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native
  helper_fields Airbender.Compiler.HelperNative.BlakeRoundCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native
  inputs 763

end Airbender.Compiler.MemoryExecuteNative.BlakeRoundCached
