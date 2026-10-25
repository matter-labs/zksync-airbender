import GKRProtocol.MemoryExecuteImport
import GKRProtocol.MemoryFrameNative.JumpBranchUncached

namespace Airbender.Compiler.MemoryExecuteNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native
  helper_fields Airbender.Compiler.HelperNative.JumpBranchUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native
  inputs 55

end Airbender.Compiler.MemoryExecuteNative.JumpBranchUncached
