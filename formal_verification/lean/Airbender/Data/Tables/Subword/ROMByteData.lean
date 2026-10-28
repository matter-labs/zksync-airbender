import Airbender.Review.Helpers.Tables.Range
import Airbender.Import.SetupRegionEmbed

namespace Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_slice subwordROMByteData from "artifacts/setup/subword-memory.json" native_table_id 45

end Airbender.Verification
