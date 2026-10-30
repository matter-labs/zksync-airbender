import Airbender.Import.SetupEmbed

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536
-- The importer checks the complete native generic table before it emits data.
set_option maxHeartbeats 4000000

import_setup_generic_columns chi5Generic from "artifacts/setup/keccak-chi5.json"
  native_table_id 66

end Airbender.Keccak.Split.Native.Fixed
