import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.KeccakCached
import Airbender.Proofs.GKRProtocol.LookupNative.KeccakCached
import Airbender.Proofs.GKRProtocol.ProductNative.KeccakCached

namespace Airbender.Compiler.FunctionalNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/keccak-cached.json"
  typing Airbender.Compiler.ConsumerNative.KeccakCached.native.typing
  lookup Airbender.Compiler.LookupNative.KeccakCached.native
  product Airbender.Compiler.ProductNative.KeccakCached.native
  base Airbender.Compiler.FullArithmeticNative.KeccakCached.native

end Airbender.Compiler.FunctionalNative.KeccakCached
