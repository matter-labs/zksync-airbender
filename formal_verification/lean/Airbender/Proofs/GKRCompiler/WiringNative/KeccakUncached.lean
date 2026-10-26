import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedGeometry
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedUnique0
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedUnique1
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedUnique2
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedPlacement0
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedPlacement1
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedPlacement2
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedPlacement3
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedGates0
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedGates1
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedGates2
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedGates3
import Airbender.Proofs.GKRCompiler.WiringParts.KeccakUncachedGates4

namespace Airbender.Compiler.WiringNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "artifacts/compiler/keccak-uncached.json" phase "assemble" start 0 count 0

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.KeccakUncached
