import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BigintUncached

namespace Airbender.Compiler.MemoryExecuteNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  memory_model Airbender.Compiler.MemoryNative.BigintUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BigintUncached.native
  helper_fields Airbender.Compiler.HelperNative.BigintUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.BigintUncached.native
  inputs 277

end Airbender.Compiler.MemoryExecuteNative.BigintUncached
