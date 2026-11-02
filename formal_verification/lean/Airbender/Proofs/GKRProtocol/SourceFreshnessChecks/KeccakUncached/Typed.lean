import Airbender.Proofs.GKRProtocol.LookupSourceNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.KeccakUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 222).map (fun index => Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank.address (Airbender.Compiler.LookupNative.KeccakUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 174, .BaseLayerWitness 173]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.KeccakUncached
