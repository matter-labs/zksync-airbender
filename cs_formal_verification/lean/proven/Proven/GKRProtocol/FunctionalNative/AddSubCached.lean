module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalNative.AddSubCachedFoundation
public import Proven.GKRProtocol.FunctionalStepChecks.AddSubCached.Certificate
public import Proven.GKRProtocol.FunctionalBaseChecks.AddSubCached.Certificate
public import Proven.Import.GKRProtocol.FunctionalFinalize

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":47,\"affine_steps\":[0,1,2,3,4,5,6,7,null,null,null,null,null,null,8,9,null,null,null,null,28,29,30,31,36,37,38,39,41,42,43,44,45,46],\"base\":[{\"affine\":8,\"gate\":0},{\"affine\":9,\"gate\":1},{\"affine\":10,\"gate\":2},{\"affine\":11,\"gate\":3},{\"affine\":12,\"gate\":4},{\"affine\":13,\"gate\":5},{\"affine\":16,\"gate\":6},{\"affine\":17,\"gate\":7},{\"affine\":18,\"gate\":8},{\"affine\":19,\"gate\":39}],\"lookup_steps\":[14,15,16,17,18,19,20,21,24,25,26,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,44,45,46],\"product_steps\":[10,11,12,13,22,23,28,29,30,31,32,33,36,37,38,39,41,42,43,44,45,46]}"
  lookup Airbender.Compiler.LookupNative.AddSubCached.native
  product Airbender.Compiler.ProductNative.AddSubCached.native
  base Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.AddSubCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.AddSubCached

end Airbender.Compiler.FunctionalNative.AddSubCached
