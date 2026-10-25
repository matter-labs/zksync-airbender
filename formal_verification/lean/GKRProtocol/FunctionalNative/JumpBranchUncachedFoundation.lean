import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.JumpBranchUncached
import GKRProtocol.LookupNative.JumpBranchUncached
import GKRProtocol.ProductNative.JumpBranchUncached

namespace Airbender.Compiler.FunctionalNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/jump-branch-uncached.json"
  typing Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing
  lookup Airbender.Compiler.LookupNative.JumpBranchUncached.native
  product Airbender.Compiler.ProductNative.JumpBranchUncached.native
  base Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native

end Airbender.Compiler.FunctionalNative.JumpBranchUncached
