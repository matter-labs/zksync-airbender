import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 10 that start in rows [0, 1073741824)
    (121 rows checked one by one). -/
theorem col10_walk : walkUpTo 512 col10Spec 0 1073741824 col10Longs 0 chi5Setup_col10 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
