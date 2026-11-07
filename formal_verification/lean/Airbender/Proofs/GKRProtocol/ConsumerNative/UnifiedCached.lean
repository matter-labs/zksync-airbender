import Airbender.Import.GKRProtocol.TypingImport
import Airbender.Proofs.GKRCompiler.WiringNative.UnifiedCached

namespace Airbender.Compiler.ConsumerNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/unified-cached.json"
  wiring Airbender.Compiler.WiringNative.UnifiedCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.UnifiedCached
