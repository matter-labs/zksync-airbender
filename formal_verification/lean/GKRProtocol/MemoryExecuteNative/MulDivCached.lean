import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.MulDivCached

namespace Airbender.Compiler.MemoryExecuteNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivCached.native
  helper_model Airbender.Compiler.HelperValidityNative.MulDivCached.native
  helper_fields Airbender.Compiler.HelperNative.MulDivCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.MulDivCached.native
  inputs 71

end Airbender.Compiler.MemoryExecuteNative.MulDivCached
