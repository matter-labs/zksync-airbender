import Airbender.Proofs.GKRProtocol.LookupSourceNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.SubwordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 62).map (fun index => Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 16, .BaseLayerWitness 14, .BaseLayerWitness 15]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.SubwordMemoryCached
