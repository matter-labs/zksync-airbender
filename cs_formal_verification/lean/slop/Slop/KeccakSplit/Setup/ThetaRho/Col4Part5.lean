import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 4 that start in rows [560000, 1073741824)
    (30066 rows checked one by one). -/
theorem col4_part5 : walkUpTo 131200 col4Spec 560000 1073741824 col4Longs 0 thetaRhoSetup_col4 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
