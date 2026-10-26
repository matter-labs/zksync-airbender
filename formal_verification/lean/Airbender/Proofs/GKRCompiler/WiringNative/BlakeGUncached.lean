import Airbender.Proofs.GKRCompiler.WiringParts.BlakeGUncachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.BlakeGUncachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.BlakeGUncachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.BlakeGUncachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.BlakeGUncachedPlacement1
import Airbender.Proofs.GKRCompiler.WiringParts.BlakeGUncachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.BlakeGUncachedGates1

namespace Airbender.Compiler.WiringNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/blake-g-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.BlakeGUncached
