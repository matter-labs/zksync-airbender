import Airbender.Data.Tables.Shift.Column2
import Airbender.Proofs.Tables.ShiftSampleChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Verification.ShiftSampleBindings
open Setup
set_option warningAsError true
set_option Elab.async false

numeric_data_binding amountBinding : (match (byteShiftColumn2.blocks[0]? : Option Block) with
  | some (.periodic _ _ values) => values
  | _ => #[]) = Airbender.Verification.ShiftSampleChecks.amount.values

end Airbender.Verification.ShiftSampleBindings
