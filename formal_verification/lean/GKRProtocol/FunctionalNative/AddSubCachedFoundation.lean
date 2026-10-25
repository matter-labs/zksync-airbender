import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.AddSubCached
import GKRProtocol.LookupNative.AddSubCached
import GKRProtocol.ProductNative.AddSubCached

namespace Airbender.Compiler.FunctionalNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/add-sub-cached.json"
  typing Airbender.Compiler.ConsumerNative.AddSubCached.native.typing
  lookup Airbender.Compiler.LookupNative.AddSubCached.native
  product Airbender.Compiler.ProductNative.AddSubCached.native
  base Airbender.Compiler.FullArithmeticNative.AddSubCached.native

end Airbender.Compiler.FunctionalNative.AddSubCached
