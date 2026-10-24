import GKRCompiler.WiringData.ShiftBinopCached

namespace Airbender.Compiler.WiringNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/shift-binop-cached.json" phase "caches" start 0 count 21

end Airbender.Compiler.WiringNative.ShiftBinopCached
