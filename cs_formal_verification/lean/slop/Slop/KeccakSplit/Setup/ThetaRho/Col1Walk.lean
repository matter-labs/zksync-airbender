import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 1 that start in rows [0, 1073741824)
    (2546 rows checked one by one). -/
theorem col1_walk : walkUpTo 512 col1Spec 0 1073741824 col1Longs 0 thetaRhoSetup_col1 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
