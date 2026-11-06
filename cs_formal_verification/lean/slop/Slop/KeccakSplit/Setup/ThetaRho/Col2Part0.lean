import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 2 that start in rows [0, 65536)
    (65536 rows checked one by one). -/
theorem col2_part0 : walkUpTo 65536 col2Spec 0 65536 col2Longs 0 thetaRhoSetup_col2 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
