import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.LookupNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.ProductNative.BlakeRoundCached

namespace Airbender.Compiler.FunctionalNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/blake-round-cached.json"
  typing Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing
  lookup Airbender.Compiler.LookupNative.BlakeRoundCached.native
  product Airbender.Compiler.ProductNative.BlakeRoundCached.native
  base Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native

end Airbender.Compiler.FunctionalNative.BlakeRoundCached
