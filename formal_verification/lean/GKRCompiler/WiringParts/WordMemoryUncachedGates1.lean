import GKRCompiler.WiringData.WordMemoryUncached

namespace Airbender.Compiler.WiringNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/word-memory-uncached.json" phase "gates" start 64 count 1

end Airbender.Compiler.WiringNative.WordMemoryUncached
