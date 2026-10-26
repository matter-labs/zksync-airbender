import Airbender.Import.GKRCompiler.Import

namespace Airbender.Compiler.Native.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_arithmetic native from "artifacts/compiler/subword-memory-uncached.json"
  certificate "artifacts/compiler/subword-memory-uncached-certificate.json"

end Airbender.Compiler.Native.SubwordMemoryUncached
