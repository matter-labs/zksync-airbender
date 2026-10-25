import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.AddSubUncached
import GKRProtocol.LookupNative.AddSubUncached
import GKRProtocol.ProductNative.AddSubUncached

namespace Airbender.Compiler.FunctionalNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/add-sub-uncached.json"
  typing Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing
  lookup Airbender.Compiler.LookupNative.AddSubUncached.native
  product Airbender.Compiler.ProductNative.AddSubUncached.native
  base Airbender.Compiler.FullArithmeticNative.AddSubUncached.native

end Airbender.Compiler.FunctionalNative.AddSubUncached
