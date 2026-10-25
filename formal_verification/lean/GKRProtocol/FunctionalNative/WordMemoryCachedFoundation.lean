import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.WordMemoryCached
import GKRProtocol.LookupNative.WordMemoryCached
import GKRProtocol.ProductNative.WordMemoryCached

namespace Airbender.Compiler.FunctionalNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/word-memory-cached.json"
  typing Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing
  lookup Airbender.Compiler.LookupNative.WordMemoryCached.native
  product Airbender.Compiler.ProductNative.WordMemoryCached.native
  base Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native

end Airbender.Compiler.FunctionalNative.WordMemoryCached
