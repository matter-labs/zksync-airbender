import GKRProtocol.FunctionalImport
import GKRProtocol.FullArithmeticNative.JumpBranchCached
import GKRProtocol.LookupNative.JumpBranchCached
import GKRProtocol.ProductNative.JumpBranchCached

namespace Airbender.Compiler.FunctionalNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/jump-branch-cached.json"
  typing Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing
  lookup Airbender.Compiler.LookupNative.JumpBranchCached.native
  product Airbender.Compiler.ProductNative.JumpBranchCached.native
  base Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native

end Airbender.Compiler.FunctionalNative.JumpBranchCached
