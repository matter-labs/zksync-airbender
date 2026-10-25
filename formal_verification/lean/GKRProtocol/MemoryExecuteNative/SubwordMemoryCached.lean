import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.SubwordMemoryCached

namespace Airbender.Compiler.MemoryExecuteNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  memory_model Airbender.Compiler.MemoryNative.SubwordMemoryCached.native
  helper_model Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native
  helper_fields Airbender.Compiler.HelperNative.SubwordMemoryCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native
  inputs 68

end Airbender.Compiler.MemoryExecuteNative.SubwordMemoryCached
