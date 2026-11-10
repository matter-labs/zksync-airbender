import Airbender.Proofs.GKRProtocol.LookupSourceNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.ShiftBinopCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 92).map (fun index => Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 27, .BaseLayerWitness 25, .BaseLayerWitness 26]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.ShiftBinopCached
