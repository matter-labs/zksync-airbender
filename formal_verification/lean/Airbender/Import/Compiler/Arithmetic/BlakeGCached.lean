import Airbender.Import.GKRCompiler.Import

namespace Airbender.Compiler.Native.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_arithmetic native from "artifacts/compiler/blake-g-cached.json"
  certificate "artifacts/compiler/blake-g-cached-certificate.json"

end Airbender.Compiler.Native.BlakeGCached
