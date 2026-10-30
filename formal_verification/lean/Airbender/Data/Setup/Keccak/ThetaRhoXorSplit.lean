import Airbender.Import.SetupLiteralTree

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536

/- Retain the native XOR-and-split region and all nine physical columns. -/
import_setup_literal_tree thetaRhoXorSplit from "artifacts/setup/keccak-theta-rho.json"
  native_table_id 58

end Airbender.Keccak.Split.Native.Fixed
