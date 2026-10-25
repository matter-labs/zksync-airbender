import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.KeccakUncached
import GKRProtocol.LookupNative.KeccakUncached
import GKRProtocol.ProductNative.KeccakUncached

namespace Airbender.Compiler.FunctionalNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/keccak-uncached.json"
  typing Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing
  lookup Airbender.Compiler.LookupNative.KeccakUncached.native
  product Airbender.Compiler.ProductNative.KeccakUncached.native
  base Airbender.Compiler.FullArithmeticNative.KeccakUncached.native

end Airbender.Compiler.FunctionalNative.KeccakUncached
