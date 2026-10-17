import Airbender.Review.Helpers.Tables.Range
import Airbender.Import.SetupRegionEmbed

namespace Airbender.UnifiedReduced.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_slice nativeRotate16Data from "artifacts/setup/unified.json" native_table_id 47

end Airbender.UnifiedReduced.Setup
