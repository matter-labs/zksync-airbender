import Airbender.Import.GKRSetupEmbed

namespace Airbender.Data.GKRSetup.ShiftBinop
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_full_setup_packed_bytes setup from "artifacts/setup/shift-binop.json" native_table_id 7 physical_column 2

theorem trace_length : setup.data.length = 16777216 := rfl
theorem range16_length : setup.range16.length = setup.data.length := rfl
theorem timestamp_length : setup.timestampRange.length = setup.data.length := rfl

end Airbender.Data.GKRSetup.ShiftBinop
