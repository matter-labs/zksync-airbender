import Airbender.Proofs.GKRProtocol.LookupSourceNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks

namespace Airbender.Compiler.SourceFreshnessChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def sourceAddresses := (List.range 632).map (fun index => Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement index))
def targetAddresses : List GKRAddress := [.BaseLayerWitness 537, .BaseLayerWitness 536]
noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress

end Airbender.Compiler.SourceFreshnessChecks.BlakeRoundUncached
