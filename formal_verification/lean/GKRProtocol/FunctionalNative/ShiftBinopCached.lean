import GKRProtocol.FunctionalNative.ShiftBinopCachedFoundation
import GKRProtocol.FunctionalNative.ShiftBinopCachedSteps0
import GKRProtocol.FunctionalNative.ShiftBinopCachedSteps1
import GKRProtocol.FunctionalNative.ShiftBinopCachedBase0
import GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":51,\"affine_steps\":[0,1,2,3,4,5,6,7,null,null,null,null,null,null,8,9,10,11,12,13,14,null,null,null,null,30,31,38,39,41,42,43,44,47,48,49,50],\"base\":[{\"affine\":8,\"gate\":0},{\"affine\":9,\"gate\":1},{\"affine\":10,\"gate\":2},{\"affine\":11,\"gate\":3},{\"affine\":12,\"gate\":4},{\"affine\":13,\"gate\":5},{\"affine\":21,\"gate\":6},{\"affine\":22,\"gate\":47},{\"affine\":23,\"gate\":48},{\"affine\":24,\"gate\":61}],\"lookup_steps\":[19,20,21,22,23,24,27,28,29,30,31,32,33,34,37,38,39,40,41,42,43,44,45,46,47,48,49,50],\"product_steps\":[15,16,17,18,25,26,30,31,35,36,38,39,41,42,43,44,47,48,49,50]}"
  lookup Airbender.Compiler.LookupNative.ShiftBinopCached.native
  product Airbender.Compiler.ProductNative.ShiftBinopCached.native
  base Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native

end Airbender.Compiler.FunctionalNative.ShiftBinopCached
