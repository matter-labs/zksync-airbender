import GKRProtocol.FunctionalNative.AddSubUncachedFoundation
import GKRProtocol.FunctionalNative.AddSubUncachedSteps0
import GKRProtocol.FunctionalNative.AddSubUncachedSteps1
import GKRProtocol.FunctionalNative.AddSubUncachedBase0
import GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":37,\"affine_steps\":[null,null,null,null,18,19,20,21,26,27,28,29,31,32,33,34,35,36],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":1},{\"affine\":2,\"gate\":2},{\"affine\":3,\"gate\":33}],\"lookup_steps\":[4,5,6,7,8,9,10,11,14,15,16,17,18,19,20,21,24,25,26,27,28,29,30,31,32,33,34,35,36],\"product_steps\":[0,1,2,3,12,13,18,19,20,21,22,23,26,27,28,29,31,32,33,34,35,36]}"
  lookup Airbender.Compiler.LookupNative.AddSubUncached.native
  product Airbender.Compiler.ProductNative.AddSubUncached.native
  base Airbender.Compiler.FullArithmeticNative.AddSubUncached.native

end Airbender.Compiler.FunctionalNative.AddSubUncached
