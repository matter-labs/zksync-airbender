import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 5 that start in rows [360000, 480000)
    (120000 rows checked one by one). -/
theorem col5_part3 : walkUpTo 65536 col5Spec 360000 480000 col5Longs 0 chi5Setup_col5 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
