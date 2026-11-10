import Airbender.Import.GKRProtocol.TypingImport
import Airbender.Proofs.GKRCompiler.WiringNative.MulDivCached

namespace Airbender.Compiler.ConsumerNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/mul-div-cached.json"
  wiring Airbender.Compiler.WiringNative.MulDivCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.MulDivCached
