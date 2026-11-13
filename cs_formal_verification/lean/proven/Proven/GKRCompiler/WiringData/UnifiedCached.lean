module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRCompiler.WiringImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringNative.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/unified-cached.json" phase "data" start 0 count 0

end Airbender.Compiler.WiringNative.UnifiedCached
