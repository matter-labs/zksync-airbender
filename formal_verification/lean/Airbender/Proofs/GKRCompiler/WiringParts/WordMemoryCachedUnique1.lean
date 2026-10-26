import Airbender.Proofs.GKRCompiler.WiringData.WordMemoryCached

namespace Airbender.Compiler.WiringNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/word-memory-cached.json" phase "unique" start 64 count 16

end Airbender.Compiler.WiringNative.WordMemoryCached
