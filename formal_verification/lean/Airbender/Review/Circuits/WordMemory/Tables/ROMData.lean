import Airbender.Review.Helpers.Tables.Range
import Airbender.Import.SetupRegionEmbed

namespace Airbender.Trace.ROM
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_slice nativeWordData from "artifacts/setup/word-memory.json" native_table_id 34

end Airbender.Trace.ROM
