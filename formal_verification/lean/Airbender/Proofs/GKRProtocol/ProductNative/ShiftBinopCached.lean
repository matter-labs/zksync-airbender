import Airbender.Import.GKRProtocol.NativeProductImport
import Airbender.Proofs.GKRProtocol.ConsumerNative.ShiftBinopCached

namespace Airbender.Compiler.ProductNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/shift-binop-cached.json"

end Airbender.Compiler.ProductNative.ShiftBinopCached
