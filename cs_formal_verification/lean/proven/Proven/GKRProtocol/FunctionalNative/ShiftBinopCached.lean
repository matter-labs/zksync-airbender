module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalNative.ShiftBinopCachedFoundation
public import Proven.GKRProtocol.FunctionalStepChecks.ShiftBinopCached.Certificate
public import Proven.GKRProtocol.FunctionalBaseChecks.ShiftBinopCached.Certificate
public import Proven.Import.GKRProtocol.FunctionalFinalize

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native from "artifacts/compiler/shift-binop-cached.json"
  lookup Airbender.Compiler.LookupNative.ShiftBinopCached.native
  product Airbender.Compiler.ProductNative.ShiftBinopCached.native
  base Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  using_steps Airbender.Compiler.FunctionalStepChecks.ShiftBinopCached.programChecked
  using_base Airbender.Compiler.FunctionalBaseChecks.ShiftBinopCached

end Airbender.Compiler.FunctionalNative.ShiftBinopCached
