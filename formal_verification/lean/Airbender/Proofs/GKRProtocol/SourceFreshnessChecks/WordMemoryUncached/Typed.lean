import Airbender.Proofs.GKRProtocol.LookupSourceNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 46).map (fun index => Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address (Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 10, .BaseLayerWitness 8, .BaseLayerWitness 9]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.WordMemoryUncached
