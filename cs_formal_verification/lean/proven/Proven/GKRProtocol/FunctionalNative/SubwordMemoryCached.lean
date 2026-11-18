module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalNative.SubwordMemoryCachedFoundation
public import Proven.GKRProtocol.FunctionalStepChecks.SubwordMemoryCached.Certificate
public import Proven.GKRProtocol.FunctionalBaseChecks.SubwordMemoryCached.Certificate
public import Proven.Import.GKRProtocol.FunctionalFinalize

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native from "artifacts/compiler/subword-memory-cached.json"
  lookup Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  product Airbender.Compiler.ProductNative.SubwordMemoryCached.native
  base Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.SubwordMemoryCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.SubwordMemoryCached

end Airbender.Compiler.FunctionalNative.SubwordMemoryCached
