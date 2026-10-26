import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeGUncached

namespace Airbender.Compiler.MemoryExecuteNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeGUncached.native
  helper_fields Airbender.Compiler.HelperNative.BlakeGUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native
  inputs 113

end Airbender.Compiler.MemoryExecuteNative.BlakeGUncached
