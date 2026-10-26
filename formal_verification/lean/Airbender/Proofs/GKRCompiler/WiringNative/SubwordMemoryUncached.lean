import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryUncachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryUncachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryUncachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryUncachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryUncachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.SubwordMemoryUncachedGates1

namespace Airbender.Compiler.WiringNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/subword-memory-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.SubwordMemoryUncached
