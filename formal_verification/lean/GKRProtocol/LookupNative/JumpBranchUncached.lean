import GKRProtocol.NativeLookupImport
import GKRProtocol.ConsumerNative.JumpBranchUncached

namespace Airbender.Compiler.LookupNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/jump-branch-uncached.json"

end Airbender.Compiler.LookupNative.JumpBranchUncached
