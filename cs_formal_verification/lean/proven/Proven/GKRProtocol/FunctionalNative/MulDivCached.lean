module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalNative.MulDivCachedFoundation
public import Proven.GKRProtocol.FunctionalStepChecks.MulDivCached.Certificate
public import Proven.GKRProtocol.FunctionalBaseChecks.MulDivCached.Certificate
public import Proven.Import.GKRProtocol.FunctionalFinalize

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native from "artifacts/compiler/mul-div-cached.json"
  lookup Airbender.Compiler.LookupNative.MulDivCached.native
  product Airbender.Compiler.ProductNative.MulDivCached.native
  base Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.MulDivCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.MulDivCached

end Airbender.Compiler.FunctionalNative.MulDivCached
