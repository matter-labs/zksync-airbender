import Airbender.Proofs.GKRProtocol.LookupSourceNative.BigintCached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 216).map (fun index => Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.address (Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 159, .BaseLayerWitness 157, .BaseLayerWitness 158]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.BigintCached
