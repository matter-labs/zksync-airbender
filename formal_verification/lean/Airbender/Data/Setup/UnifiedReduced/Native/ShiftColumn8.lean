import Airbender.Data.Setup.UnifiedReduced.Native.Source

namespace Airbender.UnifiedReduced.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_column nativeShiftColumn8 from "artifacts/setup/unified.json"
  native_table_id 9 physical_column 8 source_bytes nativeUnifiedSourceBytes

end Airbender.UnifiedReduced.Setup
