import Airbender.Proofs.GKRCompiler.WiringParts.JumpBranchCachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.JumpBranchCachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.JumpBranchCachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.JumpBranchCachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.JumpBranchCachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.JumpBranchCachedGates1
import Airbender.Proofs.GKRCompiler.WiringParts.JumpBranchCachedCaches0

namespace Airbender.Compiler.WiringNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/jump-branch-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.JumpBranchCached
