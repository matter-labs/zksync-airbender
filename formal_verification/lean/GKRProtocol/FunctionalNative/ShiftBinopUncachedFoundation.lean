import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.ShiftBinopUncached
import GKRProtocol.LookupNative.ShiftBinopUncached
import GKRProtocol.ProductNative.ShiftBinopUncached

namespace Airbender.Compiler.FunctionalNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/shift-binop-uncached.json"
  typing Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing
  lookup Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  product Airbender.Compiler.ProductNative.ShiftBinopUncached.native
  base Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native

end Airbender.Compiler.FunctionalNative.ShiftBinopUncached
