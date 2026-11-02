import Airbender.Proofs.GKRProtocol.LookupSourceNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.JumpBranchUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 49).map (fun index => Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 28, .BaseLayerWitness 26, .BaseLayerWitness 27]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.JumpBranchUncached
