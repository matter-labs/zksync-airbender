import Airbender.Import.GKRProtocol.TypingImport
import Airbender.Proofs.GKRCompiler.WiringNative.WordMemoryCached

namespace Airbender.Compiler.ConsumerNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/word-memory-cached.json"
  wiring Airbender.Compiler.WiringNative.WordMemoryCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.WordMemoryCached
