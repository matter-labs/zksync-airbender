import Airbender.Import.SetupEmbed

namespace Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

-- Complete generic-table extent; physical padding after the last native table
-- is excluded by the importer.
import_setup_generic thetaRhoGeneric from "artifacts/setup/keccak-theta-rho.json"

end Airbender.Keccak.Split.Native.Fixed
