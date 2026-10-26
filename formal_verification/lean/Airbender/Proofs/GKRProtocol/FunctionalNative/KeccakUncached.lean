import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakUncachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakUncachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakUncachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakUncachedSteps2
import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakUncachedSteps3
import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakUncachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":113,\"affine_steps\":[null,null,null,78,79,null,93,94,null,106,107,109,110,111,112],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":1},{\"affine\":2,\"gate\":194},{\"affine\":5,\"gate\":195},{\"affine\":8,\"gate\":196}],\"lookup_steps\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,84,85,86,87,88,89,90,91,92,93,94,97,98,99,100,101,104,105,106,107,108,109,110,111,112],\"product_steps\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,52,53,54,55,56,57,58,59,78,79,80,81,82,83,93,94,95,96,102,103,106,107,109,110,111,112]}"
  lookup Airbender.Compiler.LookupNative.KeccakUncached.native
  product Airbender.Compiler.ProductNative.KeccakUncached.native
  base Airbender.Compiler.FullArithmeticNative.KeccakUncached.native

end Airbender.Compiler.FunctionalNative.KeccakUncached
