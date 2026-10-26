import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.WordMemoryUncached

namespace Airbender.Compiler.MemoryExecuteNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native
  helper_fields Airbender.Compiler.HelperNative.WordMemoryUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native
  inputs 52

end Airbender.Compiler.MemoryExecuteNative.WordMemoryUncached
