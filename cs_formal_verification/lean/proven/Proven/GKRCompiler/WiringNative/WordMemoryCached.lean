module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRCompiler.WiringImport
public import Proven.GKRCompiler.WiringCheckNative.WordMemoryCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_compiler_wiring native from "artifacts/compiler/word-memory-cached.json" phase "certified" start 0 count 0 using Airbender.Compiler.WiringCheckNative.WordMemoryCached

theorem wiring_valid : native.graph.Valid := native.sound

end Airbender.Compiler.WiringNative.WordMemoryCached
