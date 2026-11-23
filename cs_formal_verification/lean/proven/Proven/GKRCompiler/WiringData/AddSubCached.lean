module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRCompiler.WiringImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringNative.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/add-sub-cached.json" phase "data" start 0 count 0

end Airbender.Compiler.WiringNative.AddSubCached
