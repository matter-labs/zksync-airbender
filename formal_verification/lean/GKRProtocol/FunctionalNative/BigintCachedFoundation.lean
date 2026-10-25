import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.BigintCached
import GKRProtocol.LookupNative.BigintCached
import GKRProtocol.ProductNative.BigintCached

namespace Airbender.Compiler.FunctionalNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/bigint-cached.json"
  typing Airbender.Compiler.ConsumerNative.BigintCached.native.typing
  lookup Airbender.Compiler.LookupNative.BigintCached.native
  product Airbender.Compiler.ProductNative.BigintCached.native
  base Airbender.Compiler.FullArithmeticNative.BigintCached.native

end Airbender.Compiler.FunctionalNative.BigintCached
