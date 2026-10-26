import Airbender.Proofs.GKRProtocol.FunctionalNative.SubwordMemoryUncachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.SubwordMemoryUncachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.SubwordMemoryUncachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.SubwordMemoryUncachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":34,\"affine_steps\":[null,null,null,null,null,null,null,null,null,17,18,24,25,28,29,30,31,32,33],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":6},{\"affine\":2,\"gate\":7},{\"affine\":3,\"gate\":9},{\"affine\":4,\"gate\":13},{\"affine\":5,\"gate\":15},{\"affine\":6,\"gate\":18},{\"affine\":7,\"gate\":19},{\"affine\":8,\"gate\":43}],\"lookup_steps\":[4,5,6,7,8,9,10,13,14,15,16,17,18,19,22,23,24,25,26,27,28,29,30,31,32,33],\"product_steps\":[0,1,2,3,11,12,17,18,20,21,24,25,28,29,30,31,32,33]}"
  lookup Airbender.Compiler.LookupNative.SubwordMemoryUncached.native
  product Airbender.Compiler.ProductNative.SubwordMemoryUncached.native
  base Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native

end Airbender.Compiler.FunctionalNative.SubwordMemoryUncached
