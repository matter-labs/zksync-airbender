import Airbender.Proofs.GKRCompiler.WiringParts.AddSubCachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubCachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubCachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubCachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubCachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubCachedGates1
import Airbender.Proofs.GKRCompiler.WiringParts.AddSubCachedCaches0

namespace Airbender.Compiler.WiringNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/add-sub-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.AddSubCached
