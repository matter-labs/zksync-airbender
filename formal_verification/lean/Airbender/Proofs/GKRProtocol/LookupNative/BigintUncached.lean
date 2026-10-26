import Airbender.Import.GKRProtocol.NativeLookupImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.BigintUncached

namespace Airbender.Compiler.LookupNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/bigint-uncached.json"

end Airbender.Compiler.LookupNative.BigintUncached
