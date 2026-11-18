module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalNative.WordMemoryCachedFoundation
public import Proven.GKRProtocol.FunctionalStepChecks.WordMemoryCached.Certificate
public import Proven.GKRProtocol.FunctionalBaseChecks.WordMemoryCached.Certificate
public import Proven.Import.GKRProtocol.FunctionalFinalize

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native from "artifacts/compiler/word-memory-cached.json"
  lookup Airbender.Compiler.LookupNative.WordMemoryCached.native
  product Airbender.Compiler.ProductNative.WordMemoryCached.native
  base Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.WordMemoryCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.WordMemoryCached

end Airbender.Compiler.FunctionalNative.WordMemoryCached
