module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.TypingImport
public import Proven.GKRCompiler.WiringNative.UnifiedCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.ConsumerNative.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/unified-cached.json"
  wiring Airbender.Compiler.WiringNative.UnifiedCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.UnifiedCached
