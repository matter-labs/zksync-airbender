import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.WordMemoryCached

namespace Airbender.Compiler.MemoryExecuteNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryCached.native
  helper_model Airbender.Compiler.HelperValidityNative.WordMemoryCached.native
  helper_fields Airbender.Compiler.HelperNative.WordMemoryCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native
  inputs 52

end Airbender.Compiler.MemoryExecuteNative.WordMemoryCached
