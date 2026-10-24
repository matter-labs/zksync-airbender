import GKRCompiler.WiringParts.JumpBranchCachedGeometry
import GKRCompiler.WiringParts.JumpBranchCachedUnique0
import GKRCompiler.WiringParts.JumpBranchCachedUnique1
import GKRCompiler.WiringParts.JumpBranchCachedPlacement0
import GKRCompiler.WiringParts.JumpBranchCachedGates0
import GKRCompiler.WiringParts.JumpBranchCachedGates1
import GKRCompiler.WiringParts.JumpBranchCachedCaches0

namespace Airbender.Compiler.WiringNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/jump-branch-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.JumpBranchCached
