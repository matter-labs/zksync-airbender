import GKRCompiler.WiringData.KeccakUncached

namespace Airbender.Compiler.WiringNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/keccak-uncached.json" phase "unique" start 64 count 64

end Airbender.Compiler.WiringNative.KeccakUncached
