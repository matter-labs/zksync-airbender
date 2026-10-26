import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.MulDivCached
import Airbender.Proofs.GKRProtocol.LookupNative.MulDivCached
import Airbender.Proofs.GKRProtocol.ProductNative.MulDivCached

namespace Airbender.Compiler.FunctionalNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/mul-div-cached.json"
  typing Airbender.Compiler.ConsumerNative.MulDivCached.native.typing
  lookup Airbender.Compiler.LookupNative.MulDivCached.native
  product Airbender.Compiler.ProductNative.MulDivCached.native
  base Airbender.Compiler.FullArithmeticNative.MulDivCached.native

end Airbender.Compiler.FunctionalNative.MulDivCached
