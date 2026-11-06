import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 8 that start in rows [0, 1073741824)
    (242 rows checked one by one). -/
theorem col8_walk : walkUpTo 512 col8Spec 0 1073741824 col8Longs 0 thetaRhoSetup_col8 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
