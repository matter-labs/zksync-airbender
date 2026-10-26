import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedPlacement1
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedGates1
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivCachedCaches0

namespace Airbender.Compiler.WiringNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/mul-div-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.MulDivCached
