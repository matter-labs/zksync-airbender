import Airbender.Proofs.GKRCompiler.WiringCheckNative.WordMemoryUncachedData
import Airbender.Proofs.GKRCompiler.WiringData.WordMemoryUncached
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.WiringCheckNative.WordMemoryUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

numeric_data_binding producers_binding : producers.toList =
  WiringChecks.KeySort.sort ((Airbender.Compiler.WiringNative.WordMemoryUncached.native.graph).produced.map AddressUniqueChecks.addressCode)
numeric_data_binding placements_binding : placements.toList =
  WiringChecks.KeySort.sort ((Airbender.Compiler.WiringNative.WordMemoryUncached.native.graph).placement.map (fun entry => AddressUniqueChecks.addressCode entry.1))
theorem bindings : WiringChecks.Bindings Airbender.Compiler.WiringNative.WordMemoryUncached.native.graph capture := ⟨producers_binding, placements_binding⟩
end Airbender.Compiler.WiringCheckNative.WordMemoryUncached
