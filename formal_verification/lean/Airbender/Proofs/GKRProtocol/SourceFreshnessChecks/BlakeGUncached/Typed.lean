import Airbender.Proofs.GKRProtocol.LookupSourceNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 83).map (fun index => Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 56, .BaseLayerWitness 55]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.BlakeGUncached
