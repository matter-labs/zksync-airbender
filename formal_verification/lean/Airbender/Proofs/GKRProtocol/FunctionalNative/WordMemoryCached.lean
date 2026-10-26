import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryCachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryCachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryCachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryCachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":44,\"affine_steps\":[0,1,2,3,4,5,6,7,null,null,null,null,null,null,8,9,10,null,null,null,null,null,null,null,null,null,26,27,28,29,34,35,38,39,40,41,42,43],\"base\":[{\"affine\":8,\"gate\":0},{\"affine\":9,\"gate\":1},{\"affine\":10,\"gate\":2},{\"affine\":11,\"gate\":3},{\"affine\":12,\"gate\":4},{\"affine\":13,\"gate\":5},{\"affine\":17,\"gate\":6},{\"affine\":18,\"gate\":10},{\"affine\":19,\"gate\":14},{\"affine\":20,\"gate\":15},{\"affine\":21,\"gate\":16},{\"affine\":22,\"gate\":31},{\"affine\":23,\"gate\":32},{\"affine\":24,\"gate\":34},{\"affine\":25,\"gate\":35}],\"lookup_steps\":[15,16,17,18,19,20,23,24,25,26,27,28,29,32,33,34,35,36,37,38,39,40,41,42,43],\"product_steps\":[11,12,13,14,21,22,26,27,28,29,30,31,34,35,38,39,40,41,42,43]}"
  lookup Airbender.Compiler.LookupNative.WordMemoryCached.native
  product Airbender.Compiler.ProductNative.WordMemoryCached.native
  base Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native

end Airbender.Compiler.FunctionalNative.WordMemoryCached
