import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryCachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryCachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryCachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryCachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryCachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryCachedGates1
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryCachedCaches0

namespace Airbender.Compiler.WiringNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/subword-memory-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.SubwordMemoryCached
