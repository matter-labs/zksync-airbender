import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.LookupNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.ProductNative.BlakeRoundUncached

namespace Airbender.Compiler.FunctionalNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/blake-round-uncached.json"
  typing Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing
  lookup Airbender.Compiler.LookupNative.BlakeRoundUncached.native
  product Airbender.Compiler.ProductNative.BlakeRoundUncached.native
  base Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native

end Airbender.Compiler.FunctionalNative.BlakeRoundUncached
