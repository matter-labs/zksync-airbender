import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.BigintCached

namespace Airbender.Compiler.MemoryExecuteNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  memory_model Airbender.Compiler.MemoryNative.BigintCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BigintCached.native
  helper_fields Airbender.Compiler.HelperNative.BigintCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.BigintCached.native
  inputs 277

end Airbender.Compiler.MemoryExecuteNative.BigintCached
