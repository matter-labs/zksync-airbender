import Airbender.Review.Helpers.Tables.Range
import Airbender.Import.SetupRegionEmbed

namespace Airbender.Trace.ROM
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_setup_slice nativeWordZeroData from "artifacts/setup/word-memory.json" native_table_id 0

end Airbender.Trace.ROM
