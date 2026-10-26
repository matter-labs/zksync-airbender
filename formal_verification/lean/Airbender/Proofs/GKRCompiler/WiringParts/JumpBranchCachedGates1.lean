import Airbender.Proofs.GKRCompiler.WiringData.JumpBranchCached

namespace Airbender.Compiler.WiringNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/jump-branch-cached.json" phase "gates" start 64 count 5

end Airbender.Compiler.WiringNative.JumpBranchCached
