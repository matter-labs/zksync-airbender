import Airbender.Import.SetupProgramEmbed

namespace Airbender.Trace.ROM
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_program subwordProgramData from "artifacts/setup/subword-memory.json"

end Airbender.Trace.ROM
