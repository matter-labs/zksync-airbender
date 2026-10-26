import Airbender.Proofs.GKRCompiler.WiringData.BlakeRoundUncached

namespace Airbender.Compiler.WiringNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/blake-round-uncached.json" phase "gates" start 576 count 44

end Airbender.Compiler.WiringNative.BlakeRoundUncached
