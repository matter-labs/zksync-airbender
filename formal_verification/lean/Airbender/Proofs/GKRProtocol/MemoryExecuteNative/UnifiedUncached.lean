import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.UnifiedUncached

namespace Airbender.Compiler.MemoryExecuteNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.UnifiedUncached.native
  helper_fields Airbender.Compiler.HelperNative.UnifiedUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native
  inputs 145

end Airbender.Compiler.MemoryExecuteNative.UnifiedUncached
