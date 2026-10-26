import Airbender.Proofs.GKRProtocol.FunctionalNative.ShiftBinopUncachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.ShiftBinopUncachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.ShiftBinopUncachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.ShiftBinopUncachedBase0
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":36,\"affine_steps\":[null,null,null,null,15,16,23,24,26,27,28,29,32,33,34,35],\"base\":[{\"affine\":0,\"gate\":0},{\"affine\":1,\"gate\":41},{\"affine\":2,\"gate\":42},{\"affine\":3,\"gate\":55}],\"lookup_steps\":[4,5,6,7,8,9,12,13,14,15,16,17,18,19,22,23,24,25,26,27,28,29,30,31,32,33,34,35],\"product_steps\":[0,1,2,3,10,11,15,16,20,21,23,24,26,27,28,29,32,33,34,35]}"
  lookup Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  product Airbender.Compiler.ProductNative.ShiftBinopUncached.native
  base Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native

end Airbender.Compiler.FunctionalNative.ShiftBinopUncached
