import Airbender.Import.SetupRegionEmbed

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 16384

/- The two native controller regions, sliced from the complete retained setup
exports by their fixed table IDs. The imported values are not regenerated from
the Rust control formulas. -/
import_setup_region thetaRhoControl from "artifacts/setup/keccak-theta-rho.json"
  native_table_id 59
import_setup_region chi5Control from "artifacts/setup/keccak-chi5.json"
  native_table_id 66

end Airbender.Keccak.Split.Native.Fixed
