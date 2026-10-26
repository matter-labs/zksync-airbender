import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.LookupNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.ProductNative.WordMemoryCached

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
