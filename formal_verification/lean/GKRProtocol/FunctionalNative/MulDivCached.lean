import GKRProtocol.FunctionalNative.MulDivCachedFoundation
import GKRProtocol.FunctionalNative.MulDivCachedSteps0
import GKRProtocol.FunctionalNative.MulDivCachedSteps1
import GKRProtocol.FunctionalNative.MulDivCachedBase0
import GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":63,\"affine_steps\":[0,1,2,3,4,5,6,7,null,null,null,null,null,null,8,9,10,11,12,13,14,15,16,17,null,null,null,null,null,null,null,null,null,null,null,null,null,38,39,42,43,50,51,53,54,56,57,61,62],\"base\":[{\"affine\":8,\"gate\":0},{\"affine\":9,\"gate\":1},{\"affine\":10,\"gate\":2},{\"affine\":11,\"gate\":3},{\"affine\":12,\"gate\":4},{\"affine\":13,\"gate\":5},{\"affine\":24,\"gate\":6},{\"affine\":25,\"gate\":19},{\"affine\":26,\"gate\":20},{\"affine\":27,\"gate\":21},{\"affine\":28,\"gate\":22},{\"affine\":29,\"gate\":23},{\"affine\":30,\"gate\":24},{\"affine\":31,\"gate\":25},{\"affine\":32,\"gate\":26},{\"affine\":33,\"gate\":27},{\"affine\":34,\"gate\":28},{\"affine\":35,\"gate\":29},{\"affine\":36,\"gate\":42}],\"lookup_steps\":[22,23,24,25,26,27,28,29,30,31,32,33,36,37,38,39,40,41,42,43,44,45,46,49,50,51,52,53,54,55,56,57,58,59,60,61,62],\"product_steps\":[18,19,20,21,34,35,38,39,42,43,47,48,50,51,53,54,56,57,61,62]}"
  lookup Airbender.Compiler.LookupNative.MulDivCached.native
  product Airbender.Compiler.ProductNative.MulDivCached.native
  base Airbender.Compiler.FullArithmeticNative.MulDivCached.native

end Airbender.Compiler.FunctionalNative.MulDivCached
