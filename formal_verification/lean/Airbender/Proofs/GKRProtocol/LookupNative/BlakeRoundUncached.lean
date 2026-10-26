import Airbender.Import.GKRProtocol.NativeLookupImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.BlakeRoundUncached

namespace Airbender.Compiler.LookupNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_lookups native from "artifacts/compiler/blake-round-uncached.json"

end Airbender.Compiler.LookupNative.BlakeRoundUncached
