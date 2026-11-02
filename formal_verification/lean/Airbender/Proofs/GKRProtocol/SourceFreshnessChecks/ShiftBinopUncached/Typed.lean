import Airbender.Proofs.GKRProtocol.LookupSourceNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 92).map (fun index => Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 27, .BaseLayerWitness 25, .BaseLayerWitness 26]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.ShiftBinopUncached
