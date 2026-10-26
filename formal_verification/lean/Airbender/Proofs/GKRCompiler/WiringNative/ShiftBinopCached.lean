import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedPlacement1
import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedGates1
import Airbender.Proofs.GKRCompiler.WiringParts.ShiftBinopCachedCaches0

namespace Airbender.Compiler.WiringNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/shift-binop-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.ShiftBinopCached
