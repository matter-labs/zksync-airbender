import GKRProtocol.TypingImport
import GKRCompiler.WiringNative.ShiftBinopCached

namespace Airbender.Compiler.ConsumerNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/shift-binop-cached.json"
  wiring Airbender.Compiler.WiringNative.ShiftBinopCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.ShiftBinopCached
