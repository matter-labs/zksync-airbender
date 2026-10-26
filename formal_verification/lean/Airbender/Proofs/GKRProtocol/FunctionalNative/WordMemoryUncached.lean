import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryUncachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryUncachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryUncachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryUncachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":33,\"affine_steps\":[null,null,null,null,null,null,null,null,null,15,16,17,18,23,24,27,28,29,30,31,32],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":4},{\"affine\":2,\"gate\":8},{\"affine\":3,\"gate\":9},{\"affine\":4,\"gate\":10},{\"affine\":5,\"gate\":25},{\"affine\":6,\"gate\":26},{\"affine\":7,\"gate\":28},{\"affine\":8,\"gate\":29}],\"lookup_steps\":[4,5,6,7,8,9,12,13,14,15,16,17,18,21,22,23,24,25,26,27,28,29,30,31,32],\"product_steps\":[0,1,2,3,10,11,15,16,17,18,19,20,23,24,27,28,29,30,31,32]}"
  lookup Airbender.Compiler.LookupNative.WordMemoryUncached.native
  product Airbender.Compiler.ProductNative.WordMemoryUncached.native
  base Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native

end Airbender.Compiler.FunctionalNative.WordMemoryUncached
