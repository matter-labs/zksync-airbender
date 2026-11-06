import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 4 that start in rows [212992, 294912)
    (81920 rows checked one by one). -/
theorem col4_part1 : walkUpTo 131200 col4Spec 212992 294912 col4Longs 0 thetaRhoSetup_col4 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
