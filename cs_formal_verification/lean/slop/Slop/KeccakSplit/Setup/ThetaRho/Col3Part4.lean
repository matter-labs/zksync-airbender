import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 3 that start in rows [424960, 458752)
    (33792 rows checked one by one). -/
theorem col3_part4 : walkUpTo 65536 col3Spec 424960 458752 col3Longs 0 thetaRhoSetup_col3 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
