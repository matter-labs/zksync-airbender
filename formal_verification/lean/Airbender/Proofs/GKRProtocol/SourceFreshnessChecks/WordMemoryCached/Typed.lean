import Airbender.Proofs.GKRProtocol.LookupSourceNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 46).map (fun index => Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 10, .BaseLayerWitness 8, .BaseLayerWitness 9]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.WordMemoryCached
