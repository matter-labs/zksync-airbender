import GKRCompiler.WiringParts.JumpBranchUncachedGeometry
import GKRCompiler.WiringParts.JumpBranchUncachedUnique0
import GKRCompiler.WiringParts.JumpBranchUncachedPlacement0
import GKRCompiler.WiringParts.JumpBranchUncachedGates0
import GKRCompiler.WiringParts.JumpBranchUncachedGates1

namespace Airbender.Compiler.WiringNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/jump-branch-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.JumpBranchUncached
