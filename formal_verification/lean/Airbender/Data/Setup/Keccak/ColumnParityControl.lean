import Airbender.Import.SetupRegionEmbed

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 16384

/- Retain the actual controller slices, including their padding rows. -/
import_setup_slice columnParitySlots from "artifacts/setup/keccak-column-parity.json"
  native_table_id 62
import_setup_slice columnParityControl from "artifacts/setup/keccak-column-parity.json"
  native_table_id 63

end Airbender.Keccak.Split.Native.Fixed
