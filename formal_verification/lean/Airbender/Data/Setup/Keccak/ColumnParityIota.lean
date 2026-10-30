import Airbender.Import.SetupRegionEmbed

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536

/- Retain every physical column of the actual native byte-iota region. -/
import_setup_slice columnParityIota from "artifacts/setup/keccak-column-parity.json"
  native_table_id 38

end Airbender.Keccak.Split.Native.Fixed
