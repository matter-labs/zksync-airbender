module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalNative.UnifiedCachedFoundation
public import Proven.GKRProtocol.FunctionalBaseChecks.UnifiedCached.Certificate
public import Proven.Import.GKRProtocol.FunctionalFinalize

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native from "artifacts/compiler/unified-cached.json"
  lookup Airbender.Compiler.LookupNative.UnifiedCached.native
  product Airbender.Compiler.ProductNative.UnifiedCached.native
  base Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  using_steps (by decide +kernel)
  using_base Airbender.Compiler.FunctionalBaseChecks.UnifiedCached

end Airbender.Compiler.FunctionalNative.UnifiedCached
