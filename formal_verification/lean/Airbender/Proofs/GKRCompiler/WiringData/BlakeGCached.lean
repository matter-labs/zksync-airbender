import Airbender.Import.GKRCompiler.WiringImport

namespace Airbender.Compiler.WiringNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/blake-g-cached.json" phase "data" start 0 count 0

end Airbender.Compiler.WiringNative.BlakeGCached
