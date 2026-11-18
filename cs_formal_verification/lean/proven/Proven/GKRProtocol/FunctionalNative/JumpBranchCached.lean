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

finalize_checked_functional_graph native from "artifacts/compiler/jump-branch-cached.json"
  lookup Airbender.Compiler.LookupNative.JumpBranchCached.native
  product Airbender.Compiler.ProductNative.JumpBranchCached.native
  base Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.JumpBranchCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.JumpBranchCached

end Airbender.Compiler.FunctionalNative.JumpBranchCached
