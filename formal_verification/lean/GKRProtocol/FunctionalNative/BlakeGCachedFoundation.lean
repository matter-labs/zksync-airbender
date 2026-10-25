import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.BlakeGCached
import GKRProtocol.LookupNative.BlakeGCached
import GKRProtocol.ProductNative.BlakeGCached

namespace Airbender.Compiler.FunctionalNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/blake-g-cached.json"
  typing Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing
  lookup Airbender.Compiler.LookupNative.BlakeGCached.native
  product Airbender.Compiler.ProductNative.BlakeGCached.native
  base Airbender.Compiler.FullArithmeticNative.BlakeGCached.native

end Airbender.Compiler.FunctionalNative.BlakeGCached
