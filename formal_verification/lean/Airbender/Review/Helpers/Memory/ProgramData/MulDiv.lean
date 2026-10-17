import Airbender.Import.SetupProgramEmbed

namespace Airbender.Trace.ROM
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_program mulDivProgramData from "artifacts/setup/mul-div.json"

end Airbender.Trace.ROM
