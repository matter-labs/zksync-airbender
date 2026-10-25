import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.KeccakCached

namespace Airbender.Compiler.MemoryExecuteNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakCached.native
  helper_model Airbender.Compiler.HelperValidityNative.KeccakCached.native
  helper_fields Airbender.Compiler.HelperNative.KeccakCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.KeccakCached.native
  inputs 267

end Airbender.Compiler.MemoryExecuteNative.KeccakCached
