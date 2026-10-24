import GKRCompiler.WiringParts.SubwordMemoryCachedGeometry
import GKRCompiler.WiringParts.SubwordMemoryCachedUnique0
import GKRCompiler.WiringParts.SubwordMemoryCachedUnique1
import GKRCompiler.WiringParts.SubwordMemoryCachedPlacement0
import GKRCompiler.WiringParts.SubwordMemoryCachedGates0
import GKRCompiler.WiringParts.SubwordMemoryCachedGates1
import GKRCompiler.WiringParts.SubwordMemoryCachedCaches0

namespace Airbender.Compiler.WiringNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/subword-memory-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.SubwordMemoryCached
