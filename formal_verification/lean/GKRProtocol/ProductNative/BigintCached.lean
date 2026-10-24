import GKRProtocol.NativeProductImport
import GKRProtocol.ConsumerNative.BigintCached

namespace Airbender.Compiler.ProductNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/bigint-cached.json"

end Airbender.Compiler.ProductNative.BigintCached
