import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.AddSubCached

namespace Airbender.Compiler.MemoryExecuteNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  memory_model Airbender.Compiler.MemoryNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperValidityNative.AddSubCached.native
  helper_fields Airbender.Compiler.HelperNative.AddSubCached.native
  frame_model Airbender.Compiler.MemoryFrameNative.AddSubCached.native
  inputs 48

end Airbender.Compiler.MemoryExecuteNative.AddSubCached
