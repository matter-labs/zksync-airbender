import Airbender.Proofs.GKRCompiler.WiringParts.AddSubUncachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubUncachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubUncachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubUncachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubUncachedGates1

namespace Airbender.Compiler.WiringNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/add-sub-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.AddSubUncached
