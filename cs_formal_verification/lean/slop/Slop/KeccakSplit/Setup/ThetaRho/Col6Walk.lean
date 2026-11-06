import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 6 that start in rows [0, 1073741824)
    (238 rows checked one by one). -/
theorem col6_walk : walkUpTo 512 col6Spec 0 1073741824 col6Longs 0 thetaRhoSetup_col6 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
