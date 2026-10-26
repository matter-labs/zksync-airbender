import Airbender.Proofs.GKRCompiler.WiringParts.MulDivUncachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivUncachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivUncachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivUncachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivUncachedPlacement1
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivUncachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.MulDivUncachedGates1

namespace Airbender.Compiler.WiringNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/mul-div-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.MulDivUncached
