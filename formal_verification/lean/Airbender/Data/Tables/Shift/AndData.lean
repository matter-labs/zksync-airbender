import Airbender.Review.Helpers.Tables.Range
import Airbender.Import.SetupRegionEmbed

namespace Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_slice_packed_bytes byteAndData from "artifacts/setup/shift-binop.json" native_table_id 7 physical_column 2

end Airbender.Verification
