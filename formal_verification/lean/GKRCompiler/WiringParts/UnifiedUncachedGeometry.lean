import GKRCompiler.WiringData.UnifiedUncached

namespace Airbender.Compiler.WiringNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/unified-uncached.json" phase "geometry" start 0 count 0

end Airbender.Compiler.WiringNative.UnifiedUncached
