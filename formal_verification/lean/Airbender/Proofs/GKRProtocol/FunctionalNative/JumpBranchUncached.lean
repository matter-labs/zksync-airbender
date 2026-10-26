import Airbender.Proofs.GKRProtocol.FunctionalNative.JumpBranchUncachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.JumpBranchUncachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.JumpBranchUncachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.JumpBranchUncachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":39,\"affine_steps\":[null,null,null,null,16,17,20,21,23,24,29,30,33,34,35,36,37,38],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":1},{\"affine\":2,\"gate\":2},{\"affine\":3,\"gate\":29}],\"lookup_steps\":[4,5,6,7,8,9,10,11,12,15,16,17,18,19,20,21,22,23,24,27,28,29,30,31,32,33,34,35,36,37,38],\"product_steps\":[0,1,2,3,13,14,16,17,20,21,23,24,25,26,29,30,33,34,35,36,37,38]}"
  lookup Airbender.Compiler.LookupNative.JumpBranchUncached.native
  product Airbender.Compiler.ProductNative.JumpBranchUncached.native
  base Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native

end Airbender.Compiler.FunctionalNative.JumpBranchUncached
