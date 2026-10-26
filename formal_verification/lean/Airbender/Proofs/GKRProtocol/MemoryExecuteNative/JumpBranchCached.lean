import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.JumpBranchCached

namespace Airbender.Compiler.MemoryExecuteNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchCached.native
  helper_model Airbender.Compiler.HelperValidityNative.JumpBranchCached.native
  helper_fields Airbender.Compiler.HelperNative.JumpBranchCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native
  inputs 55

end Airbender.Compiler.MemoryExecuteNative.JumpBranchCached
