import GKRCompiler.WiringParts.WordMemoryUncachedGeometry
import GKRCompiler.WiringParts.WordMemoryUncachedUnique0
import GKRCompiler.WiringParts.WordMemoryUncachedPlacement0
import GKRCompiler.WiringParts.WordMemoryUncachedGates0
import GKRCompiler.WiringParts.WordMemoryUncachedGates1

namespace Airbender.Compiler.WiringNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/word-memory-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.WordMemoryUncached
