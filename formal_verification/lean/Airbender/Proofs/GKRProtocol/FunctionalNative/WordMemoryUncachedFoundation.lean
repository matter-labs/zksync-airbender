import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.LookupNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.ProductNative.WordMemoryUncached

namespace Airbender.Compiler.FunctionalNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/word-memory-uncached.json"
  typing Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing
  lookup Airbender.Compiler.LookupNative.WordMemoryUncached.native
  product Airbender.Compiler.ProductNative.WordMemoryUncached.native
  base Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native

end Airbender.Compiler.FunctionalNative.WordMemoryUncached
