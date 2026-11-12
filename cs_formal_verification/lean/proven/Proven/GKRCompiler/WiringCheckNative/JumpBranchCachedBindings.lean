module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.WiringCheckNative.JumpBranchCachedData
public import Proven.GKRCompiler.WiringData.JumpBranchCached
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringCheckNative.JumpBranchCached
set_option maxRecDepth 32768

numeric_data_binding producers_binding : producers.toList =
  WiringChecks.KeySort.sort ((Airbender.Compiler.WiringNative.JumpBranchCached.native.graph).produced.map AddressUniqueChecks.addressCode)
numeric_data_binding placements_binding : placements.toList =
  WiringChecks.KeySort.sort ((Airbender.Compiler.WiringNative.JumpBranchCached.native.graph).placement.map (fun entry => AddressUniqueChecks.addressCode entry.1))
theorem bindings : WiringChecks.Bindings Airbender.Compiler.WiringNative.JumpBranchCached.native.graph capture := ⟨producers_binding, placements_binding⟩
end Airbender.Compiler.WiringCheckNative.JumpBranchCached
