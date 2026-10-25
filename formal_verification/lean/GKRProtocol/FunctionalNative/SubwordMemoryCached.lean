import GKRProtocol.FunctionalNative.SubwordMemoryCachedFoundation
import GKRProtocol.FunctionalNative.SubwordMemoryCachedSteps0
import GKRProtocol.FunctionalNative.SubwordMemoryCachedSteps1
import GKRProtocol.FunctionalNative.SubwordMemoryCachedBase0
import GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":46,\"affine_steps\":[0,1,2,3,4,5,6,7,null,null,null,null,null,null,8,9,10,11,null,null,null,null,null,null,null,null,null,29,30,36,37,40,41,42,43,44,45],\"base\":[{\"affine\":8,\"gate\":0},{\"affine\":9,\"gate\":1},{\"affine\":10,\"gate\":2},{\"affine\":11,\"gate\":3},{\"affine\":12,\"gate\":4},{\"affine\":13,\"gate\":5},{\"affine\":18,\"gate\":6},{\"affine\":19,\"gate\":12},{\"affine\":20,\"gate\":13},{\"affine\":21,\"gate\":15},{\"affine\":22,\"gate\":19},{\"affine\":23,\"gate\":21},{\"affine\":24,\"gate\":24},{\"affine\":25,\"gate\":25},{\"affine\":26,\"gate\":49}],\"lookup_steps\":[16,17,18,19,20,21,22,25,26,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,44,45],\"product_steps\":[12,13,14,15,23,24,29,30,32,33,36,37,40,41,42,43,44,45]}"
  lookup Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  product Airbender.Compiler.ProductNative.SubwordMemoryCached.native
  base Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native

end Airbender.Compiler.FunctionalNative.SubwordMemoryCached
