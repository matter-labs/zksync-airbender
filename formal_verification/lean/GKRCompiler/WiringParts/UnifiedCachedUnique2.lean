import GKRCompiler.WiringData.UnifiedCached

namespace Airbender.Compiler.WiringNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/unified-cached.json" phase "unique" start 128 count 16

end Airbender.Compiler.WiringNative.UnifiedCached
