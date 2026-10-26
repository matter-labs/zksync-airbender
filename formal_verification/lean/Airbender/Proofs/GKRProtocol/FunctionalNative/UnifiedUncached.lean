import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedUncachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedUncachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedUncachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedUncachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":51,\"affine_steps\":[null,null,null,null,25,26,30,31,37,38,40,41,42,43,47,48,49,50],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":42},{\"affine\":2,\"gate\":43},{\"affine\":3,\"gate\":132}],\"lookup_steps\":[6,7,8,9,10,11,12,13,14,15,16,19,20,21,22,23,24,25,26,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50],\"product_steps\":[0,1,2,3,4,5,17,18,25,26,30,31,32,33,37,38,40,41,42,43,47,48,49,50]}"
  lookup Airbender.Compiler.LookupNative.UnifiedUncached.native
  product Airbender.Compiler.ProductNative.UnifiedUncached.native
  base Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native

end Airbender.Compiler.FunctionalNative.UnifiedUncached
