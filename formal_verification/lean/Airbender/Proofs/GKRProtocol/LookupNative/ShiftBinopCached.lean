import Airbender.Import.GKRProtocol.NativeLookupImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.ShiftBinopCached

namespace Airbender.Compiler.LookupNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/shift-binop-cached.json"

end Airbender.Compiler.LookupNative.ShiftBinopCached
