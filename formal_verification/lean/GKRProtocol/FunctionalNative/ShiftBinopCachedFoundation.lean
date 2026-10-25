import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.ShiftBinopCached
import GKRProtocol.LookupNative.ShiftBinopCached
import GKRProtocol.ProductNative.ShiftBinopCached

namespace Airbender.Compiler.FunctionalNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/shift-binop-cached.json"
  typing Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing
  lookup Airbender.Compiler.LookupNative.ShiftBinopCached.native
  product Airbender.Compiler.ProductNative.ShiftBinopCached.native
  base Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native

end Airbender.Compiler.FunctionalNative.ShiftBinopCached
