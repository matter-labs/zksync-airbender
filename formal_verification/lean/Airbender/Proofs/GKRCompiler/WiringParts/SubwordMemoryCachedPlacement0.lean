import Airbender.Proofs.GKRCompiler.WiringData.SubwordMemoryCached

namespace Airbender.Compiler.WiringNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/subword-memory-cached.json" phase "placement" start 0 count 62

end Airbender.Compiler.WiringNative.SubwordMemoryCached
