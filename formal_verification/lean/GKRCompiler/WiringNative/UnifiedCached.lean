import GKRCompiler.WiringParts.UnifiedCachedGeometry
import GKRCompiler.WiringParts.UnifiedCachedUnique0
import GKRCompiler.WiringParts.UnifiedCachedUnique1
import GKRCompiler.WiringParts.UnifiedCachedUnique2
import GKRCompiler.WiringParts.UnifiedCachedPlacement0
import GKRCompiler.WiringParts.UnifiedCachedPlacement1
import GKRCompiler.WiringParts.UnifiedCachedPlacement2
import GKRCompiler.WiringParts.UnifiedCachedGates0
import GKRCompiler.WiringParts.UnifiedCachedGates1
import GKRCompiler.WiringParts.UnifiedCachedGates2
import GKRCompiler.WiringParts.UnifiedCachedCaches0

namespace Airbender.Compiler.WiringNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/unified-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.UnifiedCached
