import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.ShiftBinopCached

namespace Airbender.Compiler.MemoryExecuteNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopCached.native
  helper_model Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native
  helper_fields Airbender.Compiler.HelperNative.ShiftBinopCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native
  inputs 98

end Airbender.Compiler.MemoryExecuteNative.ShiftBinopCached
