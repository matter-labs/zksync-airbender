import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.UnifiedCached

namespace Airbender.Compiler.MemoryExecuteNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperValidityNative.UnifiedCached.native
  helper_fields Airbender.Compiler.HelperNative.UnifiedCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.UnifiedCached.native
  inputs 137

end Airbender.Compiler.MemoryExecuteNative.UnifiedCached
