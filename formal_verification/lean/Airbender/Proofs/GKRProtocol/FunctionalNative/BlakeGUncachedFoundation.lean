import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.LookupNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.ProductNative.BlakeGUncached

namespace Airbender.Compiler.FunctionalNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/blake-g-uncached.json"
  typing Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing
  lookup Airbender.Compiler.LookupNative.BlakeGUncached.native
  product Airbender.Compiler.ProductNative.BlakeGUncached.native
  base Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native

end Airbender.Compiler.FunctionalNative.BlakeGUncached
