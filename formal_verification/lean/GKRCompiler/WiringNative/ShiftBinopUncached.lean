import GKRCompiler.WiringParts.ShiftBinopUncachedGeometry
import GKRCompiler.WiringParts.ShiftBinopUncachedUnique0
import GKRCompiler.WiringParts.ShiftBinopUncachedUnique1
import GKRCompiler.WiringParts.ShiftBinopUncachedPlacement0
import GKRCompiler.WiringParts.ShiftBinopUncachedPlacement1
import GKRCompiler.WiringParts.ShiftBinopUncachedGates0
import GKRCompiler.WiringParts.ShiftBinopUncachedGates1

namespace Airbender.Compiler.WiringNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/shift-binop-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.ShiftBinopUncached
