import GKRProtocol.FunctionalNative.BlakeGUncachedFoundation
import GKRProtocol.FunctionalNative.BlakeGUncachedSteps0
import GKRProtocol.FunctionalNative.BlakeGUncachedSteps1
import GKRProtocol.FunctionalNative.BlakeGUncachedSteps2
import GKRProtocol.FunctionalNative.BlakeGUncachedBase0
import GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":72,\"affine_steps\":[null,null,33,36,42,43,null,50,52,58,59,null,63,64,66,67],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":35},{\"affine\":6,\"gate\":36},{\"affine\":11,\"gate\":37}],\"lookup_steps\":[10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,33,36,37,38,39,40,41,42,43,44,45,46,47,48,50,52,53,54,55,56,57,58,59,62,63,64,65,66,67,70,71],\"product_steps\":[0,1,2,3,4,5,6,7,8,9,31,32,33,34,35,36,42,43,49,50,51,52,58,59,60,61,63,64,66,67,68,69]}"
  lookup Airbender.Compiler.LookupNative.BlakeGUncached.native
  product Airbender.Compiler.ProductNative.BlakeGUncached.native
  base Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native

end Airbender.Compiler.FunctionalNative.BlakeGUncached
