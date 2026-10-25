import GKRProtocol.FunctionalNative.MulDivUncachedFoundation
import GKRProtocol.FunctionalNative.MulDivUncachedSteps0
import GKRProtocol.FunctionalNative.MulDivUncachedSteps1
import GKRProtocol.FunctionalNative.MulDivUncachedBase0
import GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":45,\"affine_steps\":[null,null,null,null,null,null,null,null,null,null,null,null,null,20,21,24,25,32,33,35,36,38,39,43,44],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":13},{\"affine\":2,\"gate\":14},{\"affine\":3,\"gate\":15},{\"affine\":4,\"gate\":16},{\"affine\":5,\"gate\":17},{\"affine\":6,\"gate\":18},{\"affine\":7,\"gate\":19},{\"affine\":8,\"gate\":20},{\"affine\":9,\"gate\":21},{\"affine\":10,\"gate\":22},{\"affine\":11,\"gate\":23},{\"affine\":12,\"gate\":36}],\"lookup_steps\":[4,5,6,7,8,9,10,11,12,13,14,15,18,19,20,21,22,23,24,25,26,27,28,31,32,33,34,35,36,37,38,39,40,41,42,43,44],\"product_steps\":[0,1,2,3,16,17,20,21,24,25,29,30,32,33,35,36,38,39,43,44]}"
  lookup Airbender.Compiler.LookupNative.MulDivUncached.native
  product Airbender.Compiler.ProductNative.MulDivUncached.native
  base Airbender.Compiler.FullArithmeticNative.MulDivUncached.native

end Airbender.Compiler.FunctionalNative.MulDivUncached
