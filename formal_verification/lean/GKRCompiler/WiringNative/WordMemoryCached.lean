import GKRCompiler.WiringParts.WordMemoryCachedGeometry
import GKRCompiler.WiringParts.WordMemoryCachedUnique0
import GKRCompiler.WiringParts.WordMemoryCachedUnique1
import GKRCompiler.WiringParts.WordMemoryCachedPlacement0
import GKRCompiler.WiringParts.WordMemoryCachedGates0
import GKRCompiler.WiringParts.WordMemoryCachedGates1
import GKRCompiler.WiringParts.WordMemoryCachedCaches0

namespace Airbender.Compiler.WiringNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/word-memory-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.WordMemoryCached
