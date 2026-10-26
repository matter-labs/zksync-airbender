import Airbender.Import.GKRProtocol.TypingImport
import Airbender.Proofs.GKRCompiler.WiringNative.WordMemoryUncached

namespace Airbender.Compiler.ConsumerNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/word-memory-uncached.json"
  wiring Airbender.Compiler.WiringNative.WordMemoryUncached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.WordMemoryUncached
