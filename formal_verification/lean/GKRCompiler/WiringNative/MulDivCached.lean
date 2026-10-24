import GKRCompiler.WiringParts.MulDivCachedGeometry
import GKRCompiler.WiringParts.MulDivCachedUnique0
import GKRCompiler.WiringParts.MulDivCachedUnique1
import GKRCompiler.WiringParts.MulDivCachedPlacement0
import GKRCompiler.WiringParts.MulDivCachedPlacement1
import GKRCompiler.WiringParts.MulDivCachedGates0
import GKRCompiler.WiringParts.MulDivCachedGates1
import GKRCompiler.WiringParts.MulDivCachedCaches0

namespace Airbender.Compiler.WiringNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/mul-div-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.MulDivCached
