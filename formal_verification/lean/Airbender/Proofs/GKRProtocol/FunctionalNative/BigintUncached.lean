import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedSteps2
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedSteps3
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedSteps4
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedSteps5
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintUncachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":192,\"affine_steps\":[null,null,null,null,null,102,103,114,115,131,132,null,135,138,145,146,152,153,null,163,165,169,170,null,183,184],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":18},{\"affine\":2,\"gate\":19},{\"affine\":3,\"gate\":20},{\"affine\":4,\"gate\":135},{\"affine\":11,\"gate\":138},{\"affine\":18,\"gate\":139},{\"affine\":23,\"gate\":140}],\"lookup_steps\":[20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,135,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,163,165,166,167,168,169,170,171,172,173,174,175,176,177,180,181,182,183,184,185,186,189,190,191],\"product_steps\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,80,81,82,83,84,85,86,87,88,89,102,103,114,115,131,132,133,134,135,136,137,138,145,146,152,153,162,163,164,165,169,170,178,179,183,184,187,188]}"
  lookup Airbender.Compiler.LookupNative.BigintUncached.native
  product Airbender.Compiler.ProductNative.BigintUncached.native
  base Airbender.Compiler.FullArithmeticNative.BigintUncached.native

end Airbender.Compiler.FunctionalNative.BigintUncached
