import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.BigintUncached
import GKRProtocol.LookupNative.BigintUncached
import GKRProtocol.ProductNative.BigintUncached

namespace Airbender.Compiler.FunctionalNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/bigint-uncached.json"
  typing Airbender.Compiler.ConsumerNative.BigintUncached.native.typing
  lookup Airbender.Compiler.LookupNative.BigintUncached.native
  product Airbender.Compiler.ProductNative.BigintUncached.native
  base Airbender.Compiler.FullArithmeticNative.BigintUncached.native

end Airbender.Compiler.FunctionalNative.BigintUncached
