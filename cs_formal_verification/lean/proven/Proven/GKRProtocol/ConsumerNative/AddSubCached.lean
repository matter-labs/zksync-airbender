module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.TypingImport
public import Proven.GKRCompiler.WiringNative.AddSubCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.ConsumerNative.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/add-sub-cached.json"
  wiring Airbender.Compiler.WiringNative.AddSubCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.AddSubCached
