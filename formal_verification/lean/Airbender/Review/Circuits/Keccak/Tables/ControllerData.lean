import Airbender.Import.SetupEmbed

namespace Airbender.Keccak
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/- All physical controller columns, including the key and native discriminator. -/
import_setup_region controllerData from "artifacts/setup/keccak.json" native_table_id 37

end Airbender.Keccak
