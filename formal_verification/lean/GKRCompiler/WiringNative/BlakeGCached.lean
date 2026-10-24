import GKRCompiler.WiringParts.BlakeGCachedGeometry
import GKRCompiler.WiringParts.BlakeGCachedUnique0
import GKRCompiler.WiringParts.BlakeGCachedUnique1
import GKRCompiler.WiringParts.BlakeGCachedUnique2
import GKRCompiler.WiringParts.BlakeGCachedPlacement0
import GKRCompiler.WiringParts.BlakeGCachedPlacement1
import GKRCompiler.WiringParts.BlakeGCachedGates0
import GKRCompiler.WiringParts.BlakeGCachedGates1
import GKRCompiler.WiringParts.BlakeGCachedCaches0

namespace Airbender.Compiler.WiringNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/blake-g-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.BlakeGCached
