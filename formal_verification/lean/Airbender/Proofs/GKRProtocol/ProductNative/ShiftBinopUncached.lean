import Airbender.Import.GKRProtocol.NativeProductImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.ShiftBinopUncached

namespace Airbender.Compiler.ProductNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/shift-binop-uncached.json"

end Airbender.Compiler.ProductNative.ShiftBinopUncached
