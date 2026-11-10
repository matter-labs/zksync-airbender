import Airbender.Import.SetupRegionEmbed

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 16384

/- Retain every physical column of the exact native slot-table region. -/
import_setup_region thetaRhoSlots from "artifacts/setup/keccak-theta-rho.json"
  native_table_id 60

end Airbender.Keccak.Split.Native.Fixed
