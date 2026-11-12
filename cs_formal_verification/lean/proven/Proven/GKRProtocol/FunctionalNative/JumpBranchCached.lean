module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalNative.JumpBranchCachedFoundation
public import Proven.GKRProtocol.FunctionalStepChecks.JumpBranchCached.Certificate
public import Proven.GKRProtocol.FunctionalBaseChecks.JumpBranchCached.Certificate
public import Proven.Import.GKRProtocol.FunctionalFinalize

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":53,\"affine_steps\":[0,1,2,3,4,5,6,7,null,null,null,null,null,null,8,9,10,11,12,13,null,null,null,null,30,31,34,35,37,38,43,44,47,48,49,50,51,52],\"base\":[{\"affine\":8,\"gate\":0},{\"affine\":9,\"gate\":1},{\"affine\":10,\"gate\":2},{\"affine\":11,\"gate\":3},{\"affine\":12,\"gate\":4},{\"affine\":13,\"gate\":5},{\"affine\":20,\"gate\":6},{\"affine\":21,\"gate\":7},{\"affine\":22,\"gate\":8},{\"affine\":23,\"gate\":35}],\"lookup_steps\":[18,19,20,21,22,23,24,25,26,29,30,31,32,33,34,35,36,37,38,41,42,43,44,45,46,47,48,49,50,51,52],\"product_steps\":[14,15,16,17,27,28,30,31,34,35,37,38,39,40,43,44,47,48,49,50,51,52]}"
  lookup Airbender.Compiler.LookupNative.JumpBranchCached.native
  product Airbender.Compiler.ProductNative.JumpBranchCached.native
  base Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.JumpBranchCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.JumpBranchCached

end Airbender.Compiler.FunctionalNative.JumpBranchCached
