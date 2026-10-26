import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedCachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedCachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedCachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedCachedSteps2
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedCachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":66,\"affine_steps\":[0,1,2,3,4,5,6,7,null,null,null,null,null,null,8,9,10,11,12,13,14,null,null,null,null,40,41,45,46,52,53,55,56,57,58,62,63,64,65],\"base\":[{\"affine\":8,\"gate\":0},{\"affine\":9,\"gate\":1},{\"affine\":10,\"gate\":2},{\"affine\":11,\"gate\":3},{\"affine\":12,\"gate\":4},{\"affine\":13,\"gate\":5},{\"affine\":21,\"gate\":6},{\"affine\":22,\"gate\":48},{\"affine\":23,\"gate\":49},{\"affine\":24,\"gate\":138}],\"lookup_steps\":[21,22,23,24,25,26,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,44,45,46,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65],\"product_steps\":[15,16,17,18,19,20,32,33,40,41,45,46,47,48,52,53,55,56,57,58,62,63,64,65]}"
  lookup Airbender.Compiler.LookupNative.UnifiedCached.native
  product Airbender.Compiler.ProductNative.UnifiedCached.native
  base Airbender.Compiler.FullArithmeticNative.UnifiedCached.native

end Airbender.Compiler.FunctionalNative.UnifiedCached
