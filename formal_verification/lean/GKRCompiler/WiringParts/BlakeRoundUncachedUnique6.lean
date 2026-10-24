import GKRCompiler.WiringData.BlakeRoundUncached

namespace Airbender.Compiler.WiringNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/blake-round-uncached.json" phase "unique" start 384 count 64

end Airbender.Compiler.WiringNative.BlakeRoundUncached
