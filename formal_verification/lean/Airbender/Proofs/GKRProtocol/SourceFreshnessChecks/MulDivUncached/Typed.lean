import Airbender.Proofs.GKRProtocol.LookupSourceNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.MulDivUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 65).map (fun index => Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address (Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 23, .BaseLayerWitness 21, .BaseLayerWitness 22]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.MulDivUncached
