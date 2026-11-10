import Airbender.Import.GKRSetupEmbed

namespace Airbender.Data.GKRSetup.AddSub
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_full_setup setup from "artifacts/setup/add-sub.json"

theorem trace_length : setup.data.length = 16777216 := rfl
theorem range16_length : setup.range16.length = setup.data.length := rfl
theorem timestamp_length : setup.timestampRange.length = setup.data.length := rfl

end Airbender.Data.GKRSetup.AddSub
