import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.ShiftBinopUncached

namespace Airbender.Compiler.MemoryExecuteNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native
  helper_fields Airbender.Compiler.HelperNative.ShiftBinopUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native
  inputs 98

end Airbender.Compiler.MemoryExecuteNative.ShiftBinopUncached
