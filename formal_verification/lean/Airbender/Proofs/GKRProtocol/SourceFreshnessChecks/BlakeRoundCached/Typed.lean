import Airbender.Proofs.GKRProtocol.LookupSourceNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 632).map (fun index => Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundCached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 537, .BaseLayerWitness 536]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached
