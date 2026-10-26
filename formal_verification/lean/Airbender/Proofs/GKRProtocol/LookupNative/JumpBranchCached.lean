import Airbender.Import.GKRProtocol.NativeLookupImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.JumpBranchCached

namespace Airbender.Compiler.LookupNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/jump-branch-cached.json"

end Airbender.Compiler.LookupNative.JumpBranchCached
