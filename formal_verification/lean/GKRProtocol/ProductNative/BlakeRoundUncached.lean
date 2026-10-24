import GKRProtocol.NativeProductImport
import GKRProtocol.ConsumerNative.BlakeRoundUncached

namespace Airbender.Compiler.ProductNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/blake-round-uncached.json"

end Airbender.Compiler.ProductNative.BlakeRoundUncached
