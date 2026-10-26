import Airbender.Import.GKRProtocol.NativeLookupImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.BigintCached

namespace Airbender.Compiler.LookupNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/bigint-cached.json"

end Airbender.Compiler.LookupNative.BigintCached
