import GKRProtocol.TypingImport
import GKRCompiler.WiringNative.BlakeGCached

namespace Airbender.Compiler.ConsumerNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/blake-g-cached.json"
  wiring Airbender.Compiler.WiringNative.BlakeGCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.BlakeGCached
