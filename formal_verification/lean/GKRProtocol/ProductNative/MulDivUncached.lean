import GKRProtocol.NativeProductImport
import GKRProtocol.ConsumerNative.MulDivUncached

namespace Airbender.Compiler.ProductNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/mul-div-uncached.json"

end Airbender.Compiler.ProductNative.MulDivUncached
