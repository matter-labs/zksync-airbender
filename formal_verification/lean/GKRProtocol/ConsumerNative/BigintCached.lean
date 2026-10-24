import GKRProtocol.TypingImport
import GKRCompiler.WiringNative.BigintCached

namespace Airbender.Compiler.ConsumerNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/bigint-cached.json"
  wiring Airbender.Compiler.WiringNative.BigintCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.BigintCached
