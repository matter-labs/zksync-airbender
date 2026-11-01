import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalBaseChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 6 = (data0.drop 0).take 6

numeric_data_binding piece0 : (data0.drop 0).take 6 = ((originalEntries.drop 0).take 6).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 6 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 6))

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 6
    (by decide +kernel) (by decide +kernel) binding0

end Airbender.Compiler.FunctionalBaseChecks.BlakeRoundUncached
