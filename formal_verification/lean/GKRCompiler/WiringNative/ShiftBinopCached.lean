import GKRCompiler.WiringParts.ShiftBinopCachedGeometry
import GKRCompiler.WiringParts.ShiftBinopCachedUnique0
import GKRCompiler.WiringParts.ShiftBinopCachedUnique1
import GKRCompiler.WiringParts.ShiftBinopCachedPlacement0
import GKRCompiler.WiringParts.ShiftBinopCachedPlacement1
import GKRCompiler.WiringParts.ShiftBinopCachedGates0
import GKRCompiler.WiringParts.ShiftBinopCachedGates1
import GKRCompiler.WiringParts.ShiftBinopCachedCaches0

namespace Airbender.Compiler.WiringNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/shift-binop-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.ShiftBinopCached
