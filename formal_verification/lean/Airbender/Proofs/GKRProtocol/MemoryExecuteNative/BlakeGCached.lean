import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeGCached

namespace Airbender.Compiler.MemoryExecuteNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeGCached.native
  helper_fields Airbender.Compiler.HelperNative.BlakeGCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.BlakeGCached.native
  inputs 113

end Airbender.Compiler.MemoryExecuteNative.BlakeGCached
