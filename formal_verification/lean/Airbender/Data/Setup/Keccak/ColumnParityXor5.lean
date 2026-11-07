import Airbender.Import.SetupLiteralTree

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/- All eight physical columns come from the complete native source. -/
import_setup_literal_tree columnParityXor5 from "artifacts/setup/keccak-column-parity.json"
  native_table_id 64

end Airbender.Keccak.Split.Native.Fixed
