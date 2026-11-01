import Airbender.Import.GKRCompiler.WiringImport
import Airbender.Proofs.GKRCompiler.WiringCheckNative.BigintUncached

namespace Airbender.Compiler.WiringNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/bigint-uncached.json" phase "certified" start 0 count 0 using Airbender.Compiler.WiringCheckNative.BigintUncached

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.BigintUncached
