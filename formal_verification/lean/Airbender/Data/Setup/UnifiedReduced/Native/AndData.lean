import Airbender.Review.Helpers.Tables.Range
import Airbender.Import.SetupRegionEmbed

namespace Airbender.UnifiedReduced.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_slice nativeAndData from "artifacts/setup/unified.json" native_table_id 54

end Airbender.UnifiedReduced.Setup
