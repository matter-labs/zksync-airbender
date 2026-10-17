import Airbender.Review.Helpers.Tables.Shift.Source

namespace Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_column byteShiftColumn6 from "artifacts/setup/shift-binop.json"
  native_table_id 9 physical_column 6 source_bytes nativeShiftSourceBytes

end Airbender.Verification
