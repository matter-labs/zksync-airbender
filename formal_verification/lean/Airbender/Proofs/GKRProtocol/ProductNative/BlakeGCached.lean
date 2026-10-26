import Airbender.Import.GKRProtocol.NativeProductImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.BlakeGCached

namespace Airbender.Compiler.ProductNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/blake-g-cached.json"

end Airbender.Compiler.ProductNative.BlakeGCached
