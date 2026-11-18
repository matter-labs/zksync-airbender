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

finalize_checked_functional_graph native from "artifacts/compiler/add-sub-cached.json"
  lookup Airbender.Compiler.LookupNative.AddSubCached.native
  product Airbender.Compiler.ProductNative.AddSubCached.native
  base Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.AddSubCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.AddSubCached

end Airbender.Compiler.FunctionalNative.AddSubCached
