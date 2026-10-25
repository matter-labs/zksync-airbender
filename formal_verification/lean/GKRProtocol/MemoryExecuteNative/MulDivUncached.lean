import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.MulDivUncached

namespace Airbender.Compiler.MemoryExecuteNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.MulDivUncached.native
  helper_fields Airbender.Compiler.HelperNative.MulDivUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.MulDivUncached.native
  inputs 71

end Airbender.Compiler.MemoryExecuteNative.MulDivUncached
