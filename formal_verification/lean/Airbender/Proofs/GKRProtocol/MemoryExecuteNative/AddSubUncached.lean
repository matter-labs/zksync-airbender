import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.AddSubUncached

namespace Airbender.Compiler.MemoryExecuteNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  memory_model Airbender.Compiler.MemoryNative.AddSubUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.AddSubUncached.native
  helper_fields Airbender.Compiler.HelperNative.AddSubUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.AddSubUncached.native
  inputs 48

end Airbender.Compiler.MemoryExecuteNative.AddSubUncached
