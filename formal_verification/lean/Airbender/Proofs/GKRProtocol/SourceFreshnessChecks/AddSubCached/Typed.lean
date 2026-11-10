import Airbender.Proofs.GKRProtocol.LookupSourceNative.AddSubCached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 42).map (fun index => Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address (Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 21, .BaseLayerWitness 19, .BaseLayerWitness 20]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.AddSubCached
