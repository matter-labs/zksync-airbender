import Airbender.Import.GKRProtocol.MemoryExecuteImport
import Airbender.Proofs.GKRProtocol.MemoryFrameNative.KeccakUncached

namespace Airbender.Compiler.MemoryExecuteNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_memory_execute native
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.KeccakUncached.native
  helper_fields Airbender.Compiler.HelperNative.KeccakUncached.native
  frame_model Airbender.Compiler.MemoryFrameNative.KeccakUncached.native
  inputs 266

end Airbender.Compiler.MemoryExecuteNative.KeccakUncached
