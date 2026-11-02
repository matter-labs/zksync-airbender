import Airbender.Proofs.GKRProtocol.LookupSourceNative.KeccakCached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 222).map (fun index => Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 174, .BaseLayerWitness 173]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.KeccakCached
