import Airbender.Proofs.GKRProtocol.LookupSourceNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 62).map (fun index => Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 16, .BaseLayerWitness 14, .BaseLayerWitness 15]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.SubwordMemoryUncached
