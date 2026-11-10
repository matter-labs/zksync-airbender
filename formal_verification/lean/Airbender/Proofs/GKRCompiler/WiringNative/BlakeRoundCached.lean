import Airbender.Import.GKRCompiler.WiringImport
import Airbender.Proofs.GKRCompiler.WiringCheckNative.BlakeRoundCached

namespace Airbender.Compiler.WiringNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/blake-round-cached.json" phase "certified" start 0 count 0 using Airbender.Compiler.WiringCheckNative.BlakeRoundCached

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.BlakeRoundCached
