import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.SubwordMemoryUncached

namespace Airbender.Compiler.MemoryExecuteNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native
  helper_fields Airbender.Compiler.HelperNative.SubwordMemoryUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native
  inputs 68

end Airbender.Compiler.MemoryExecuteNative.SubwordMemoryUncached
