import Airbender.Proofs.GKRCompiler.WiringData.BigintCached

namespace Airbender.Compiler.WiringNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/bigint-cached.json" phase "placement" start 192 count 24

end Airbender.Compiler.WiringNative.BigintCached
