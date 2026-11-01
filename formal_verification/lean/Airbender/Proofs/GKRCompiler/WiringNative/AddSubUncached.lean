import Airbender.Import.GKRCompiler.WiringImport
import Airbender.Proofs.GKRCompiler.WiringCheckNative.AddSubUncached

namespace Airbender.Compiler.WiringNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/add-sub-uncached.json" phase "certified" start 0 count 0 using Airbender.Compiler.WiringCheckNative.AddSubUncached

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.AddSubUncached
