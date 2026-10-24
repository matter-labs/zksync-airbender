import GKRProtocol.TypingImport
import GKRCompiler.WiringNative.JumpBranchCached

namespace Airbender.Compiler.ConsumerNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_typing native from "artifacts/compiler/jump-branch-cached.json"
  wiring Airbender.Compiler.WiringNative.JumpBranchCached.native

theorem consumer_types_valid : native.typing.Valid := native.sound

end Airbender.Compiler.ConsumerNative.JumpBranchCached
