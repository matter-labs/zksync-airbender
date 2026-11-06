import Slop.KeccakSplit.Setup.ThetaRho.Shapes

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 4 that start in rows [470016, 560000)
    (89984 rows checked one by one). -/
theorem col4_part4 : walkUpTo 131200 col4Spec 470016 560000 col4Longs 0 thetaRhoSetup_col4 = true := by
  decide +kernel

end Airbender.Keccak.Split.ThetaRho.SetupProofs
