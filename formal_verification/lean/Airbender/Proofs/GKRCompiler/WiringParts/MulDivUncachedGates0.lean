import Airbender.Proofs.GKRCompiler.WiringData.MulDivUncached

namespace Airbender.Compiler.WiringNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/mul-div-uncached.json" phase "gates" start 0 count 64

end Airbender.Compiler.WiringNative.MulDivUncached
