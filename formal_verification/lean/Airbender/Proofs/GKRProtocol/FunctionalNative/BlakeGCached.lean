import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeGCachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeGCachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeGCachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeGCachedSteps2
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeGCachedSteps3
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeGCachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":112,\"affine_steps\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,null,null,73,76,82,83,null,90,92,98,99,null,103,104,106,107],\"base\":[{\"affine\":20,\"gate\":0},{\"affine\":21,\"gate\":1},{\"affine\":22,\"gate\":2},{\"affine\":23,\"gate\":3},{\"affine\":24,\"gate\":4},{\"affine\":25,\"gate\":5},{\"affine\":26,\"gate\":6},{\"affine\":27,\"gate\":7},{\"affine\":28,\"gate\":8},{\"affine\":29,\"gate\":9},{\"affine\":30,\"gate\":10},{\"affine\":31,\"gate\":11},{\"affine\":32,\"gate\":12},{\"affine\":33,\"gate\":13},{\"affine\":34,\"gate\":14},{\"affine\":35,\"gate\":15},{\"affine\":36,\"gate\":16},{\"affine\":37,\"gate\":17},{\"affine\":38,\"gate\":18},{\"affine\":39,\"gate\":19},{\"affine\":40,\"gate\":20},{\"affine\":61,\"gate\":21},{\"affine\":62,\"gate\":56},{\"affine\":67,\"gate\":57},{\"affine\":72,\"gate\":58}],\"lookup_steps\":[50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,73,76,77,78,79,80,81,82,83,84,85,86,87,88,90,92,93,94,95,96,97,98,99,102,103,104,105,106,107,110,111],\"product_steps\":[40,41,42,43,44,45,46,47,48,49,71,72,73,74,75,76,82,83,89,90,91,92,98,99,100,101,103,104,106,107,108,109]}"
  lookup Airbender.Compiler.LookupNative.BlakeGCached.native
  product Airbender.Compiler.ProductNative.BlakeGCached.native
  base Airbender.Compiler.FullArithmeticNative.BlakeGCached.native

end Airbender.Compiler.FunctionalNative.BlakeGCached
