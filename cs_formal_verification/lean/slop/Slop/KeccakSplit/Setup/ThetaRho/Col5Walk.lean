import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 5 that start in rows [0, 1073741824)
    (239 rows checked one by one). -/
theorem col5_walk : walkUpTo 512 col5Spec 0 1073741824 col5Longs 0 thetaRhoSetup_col5 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
