import Airbender.Data.Tables.Subword.StorePlaceData
import Airbender.Data.Tables.Subword.LoadByteData
import Airbender.Proofs.Tables.SubwordSampleChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Verification.SubwordSampleBindings
open Setup
set_option warningAsError true
set_option Elab.async false

numeric_data_binding storeHighBinding : (match (storePlaceData.columns[1].blocks[1]? : Option Block) with
  | some (.periodic _ _ values) => values
  | _ => #[]) = Airbender.Verification.SubwordSampleChecks.storeHigh.values

numeric_data_binding byteLowBinding : (match (loadByteData.columns[1].blocks[1]? : Option Block) with
  | some (.periodic _ _ values) => values
  | _ => #[]) = Airbender.Verification.SubwordSampleChecks.byteLow.values

numeric_data_binding byteHighBinding : (match (loadByteData.columns[2].blocks[1]? : Option Block) with
  | some (.periodic _ _ values) => values
  | _ => #[]) = Airbender.Verification.SubwordSampleChecks.byteHigh.values

end Airbender.Verification.SubwordSampleBindings
