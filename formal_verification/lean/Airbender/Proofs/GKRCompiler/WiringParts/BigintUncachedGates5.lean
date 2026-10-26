import Airbender.Proofs.GKRCompiler.WiringData.BigintUncached

namespace Airbender.Compiler.WiringNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/bigint-uncached.json" phase "gates" start 320 count 14

end Airbender.Compiler.WiringNative.BigintUncached
