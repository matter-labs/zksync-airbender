module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section

namespace Airbender.Keccak.Split.ThetaRho

/- Native fixed tables of the split Keccak ThetaRho worker, read from the exported setup JSON
   (`artifacts/setup/README.md`). Columns are compressed blocks; `decode` is the row value. -/
import_setup_blocks thetaRhoSetup from "artifacts/setup/keccak-theta-rho.json"

check_native_ranges "artifacts/setup/keccak-theta-rho.json"

end Airbender.Keccak.Split.ThetaRho
