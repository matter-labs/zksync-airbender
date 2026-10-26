import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.LookupNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.ProductNative.SubwordMemoryCached

namespace Airbender.Compiler.FunctionalNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/subword-memory-cached.json"
  typing Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing
  lookup Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  product Airbender.Compiler.ProductNative.SubwordMemoryCached.native
  base Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native

end Airbender.Compiler.FunctionalNative.SubwordMemoryCached
