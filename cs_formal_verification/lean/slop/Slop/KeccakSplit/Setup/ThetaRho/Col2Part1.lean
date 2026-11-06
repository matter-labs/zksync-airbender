import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 2 that start in rows [65536, 1073741824)
    (242 rows checked one by one). -/
theorem col2_part1 : walkUpTo 512 col2Spec 65536 1073741824 col2Longs 0 thetaRhoSetup_col2 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
