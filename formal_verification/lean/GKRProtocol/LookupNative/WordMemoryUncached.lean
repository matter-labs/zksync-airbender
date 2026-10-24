import GKRProtocol.NativeLookupImport
import GKRProtocol.ConsumerNative.WordMemoryUncached

namespace Airbender.Compiler.LookupNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/word-memory-uncached.json"

end Airbender.Compiler.LookupNative.WordMemoryUncached
