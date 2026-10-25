import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.UnifiedUncached
import GKRProtocol.LookupNative.UnifiedUncached
import GKRProtocol.ProductNative.UnifiedUncached

namespace Airbender.Compiler.FunctionalNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/unified-uncached.json"
  typing Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing
  lookup Airbender.Compiler.LookupNative.UnifiedUncached.native
  product Airbender.Compiler.ProductNative.UnifiedUncached.native
  base Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native

end Airbender.Compiler.FunctionalNative.UnifiedUncached
