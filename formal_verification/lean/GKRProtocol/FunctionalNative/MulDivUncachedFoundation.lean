import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.MulDivUncached
import GKRProtocol.LookupNative.MulDivUncached
import GKRProtocol.ProductNative.MulDivUncached

namespace Airbender.Compiler.FunctionalNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/mul-div-uncached.json"
  typing Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing
  lookup Airbender.Compiler.LookupNative.MulDivUncached.native
  product Airbender.Compiler.ProductNative.MulDivUncached.native
  base Airbender.Compiler.FullArithmeticNative.MulDivUncached.native

end Airbender.Compiler.FunctionalNative.MulDivUncached
