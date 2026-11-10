import Airbender.Import.SetupLiteralTree

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536

/- Retain every physical column of the complete native byte-XOR region. -/
import_setup_literal_tree thetaRhoXor from "artifacts/setup/keccak-theta-rho.json"
  native_table_id 4

end Airbender.Keccak.Split.Native.Fixed
