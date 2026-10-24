import GKRCompiler.WiringParts.UnifiedUncachedGeometry
import GKRCompiler.WiringParts.UnifiedUncachedUnique0
import GKRCompiler.WiringParts.UnifiedUncachedUnique1
import GKRCompiler.WiringParts.UnifiedUncachedPlacement0
import GKRCompiler.WiringParts.UnifiedUncachedPlacement1
import GKRCompiler.WiringParts.UnifiedUncachedPlacement2
import GKRCompiler.WiringParts.UnifiedUncachedGates0
import GKRCompiler.WiringParts.UnifiedUncachedGates1
import GKRCompiler.WiringParts.UnifiedUncachedGates2

namespace Airbender.Compiler.WiringNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/unified-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.UnifiedUncached
