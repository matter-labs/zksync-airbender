import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedUnique2
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedUnique3
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedUnique4
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedPlacement1
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedPlacement2
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedPlacement3
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedGates1
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedGates2
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedGates3
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedGates4
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedCaches0
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakCachedCaches1

namespace Airbender.Compiler.WiringNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/keccak-cached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.KeccakCached
