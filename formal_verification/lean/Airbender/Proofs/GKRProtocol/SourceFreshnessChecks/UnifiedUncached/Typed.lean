import Airbender.Proofs.GKRProtocol.LookupSourceNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.UnifiedUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 123).map (fun index => Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address (Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 57, .BaseLayerWitness 55, .BaseLayerWitness 56]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.UnifiedUncached
