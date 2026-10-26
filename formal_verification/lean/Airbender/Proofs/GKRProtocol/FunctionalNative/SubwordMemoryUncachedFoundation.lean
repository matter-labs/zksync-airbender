import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.LookupNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.ProductNative.SubwordMemoryUncached

namespace Airbender.Compiler.FunctionalNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/subword-memory-uncached.json"
  typing Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing
  lookup Airbender.Compiler.LookupNative.SubwordMemoryUncached.native
  product Airbender.Compiler.ProductNative.SubwordMemoryUncached.native
  base Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native

end Airbender.Compiler.FunctionalNative.SubwordMemoryUncached
