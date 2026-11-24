module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRCompiler.WiringImport
public import Proven.GKRCompiler.WiringCheckNative.UnifiedCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringNative.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/unified-cached.json" phase "certified" start 0 count 0 using Airbender.Compiler.WiringCheckNative.UnifiedCached

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.UnifiedCached
